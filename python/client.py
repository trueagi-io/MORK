from typing import Optional
import os
from time import monotonic_ns, sleep
from base64 import b32encode
import re
from io import StringIO, FileIO
from urllib.parse import quote

import requests
from requests import request, RequestException
from subprocess import Popen

class MORK:
    """
    Wrapper for the MORK server-based API.
    """
    class Request:
        def __init__(self, method, subdir, **kwargs):
            self.method = method
            self.subdir = subdir
            self.kwargs = kwargs
            self.response = None
            self.error = None

        def dispatch(self, server):
            try:
                self.response = request(self.method, server.base + self.subdir, **self.kwargs)
            except RequestException as e:
                self.error = e

        def __str__(self):
            return str(vars(self))

    class Upload(Request):
        def __init__(self, pattern, template, data):
            self.pattern = pattern
            self.template = template
            self.data = data
            super().__init__("post", f"/upload/{quote(self.pattern)}/{quote(self.template)}/", data=self.data, headers={"Content-Type": "text/plain"})

    class Download(Request):
        def __init__(self, pattern, template):
            self.pattern = pattern
            self.template = template
            self.data = None
            super().__init__("get", f"/export/{quote(self.pattern)}/{quote(self.template)}/")

        def dispatch(self, server):
            super().dispatch(server)
            if self.response and self.response.status_code == 200:
                self.data = self.response.text

    class Clear(Request):
        def __init__(self, expr):
            self.expr = expr
            super().__init__("get", f"/clear/{quote(self.expr)}/")

    class Stop(Request):
        def __init__(self, wait_for_idle=False):
            self.wait_for_idle = wait_for_idle
            super().__init__("get", f"/stop/" if wait_for_idle else f"/stop/?wait_for_idle")

    class Status(Request):
        def __init__(self, pattern):
            self.pattern = pattern
            super().__init__("get", f"/status/{quote(pattern)}")

    class Import(Request):
        def __init__(self, pattern, template, file_uri):
            self.pattern = pattern
            self.template = template
            self.uri = file_uri
            super().__init__("get", f"/import/{quote(self.pattern)}/{quote(self.template)}/?uri={self.uri}")

    class Transform(Request):
        def __init__(self, patterns, templates):
            self.patterns = patterns
            self.templates = templates
            self.payload = "(transform (, {}) (, {}))".format(" ".join(patterns), " ".join(templates))
            super().__init__("post", f"/transform_multi_multi/", data=self.payload, headers={"Content-Type": "text/plain"})

    def transform(self, patterns, templates):
        u = self.Transform(tuple(map(self.ns.format, patterns)), tuple(map(self.ns.format, templates)))
        self.history.append(u)
        u.dispatch(self)
        return u

    def and_clear(self):
        self.finalization += ("clear",)
        return self

    def __init__(self, base_url: Optional[str] = os.environ.get("MORK_URL"), namespace = "{}", finalization = (), parent=None, history=None):
        if base_url is None:
            base_url = "http://127.0.0.1:8000"
        if isinstance(base_url, str):
            base_url = base_url.strip()

        self.base = base_url
        self.ns = namespace
        self.finalization = finalization
        self.parent = parent
        self.history = [] if history is None else history

        if parent is None:
            status_req = self.Status("-")
            status_req.dispatch(self)
            if status_req.response is None or status_req.response.status_code != 200:
                raise ConnectionError(f"Failed to connect to MORK server at {base_url}")

    def upload(self, data):
        io = self.ns.format("$x")
        u = self.Upload("$x", io, data)
        self.history.append(u)
        u.dispatch(self)
        return u

    def download_(self):
        io = self.ns.format("$x")
        d = self.Download(io, "$x")
        self.history.append(d)
        d.dispatch(self)
        return d

    def download(self, pattern, template):
        io = self.ns.format(pattern)
        d = self.Download(io, template)
        self.history.append(d)
        d.dispatch(self)
        return d

    def sexpr_import(self, file_uri):
        io = self.ns.format("$x")
        u = self.Import("$x", io, file_uri)
        self.history.append(u)
        u.dispatch(self)
        return u

    def clear(self):
        io = self.ns.format("$x")
        c = self.Clear(io)
        self.history.append(c)
        c.dispatch(self)
        return c

    def work_at(self, name, finalization=(), **kwargs):
        return MORK(**kwargs, namespace=f"({name} {{}})", finalization=finalization, parent=self, history=self.history)

    def __enter__(self):
        # io = self.ns.format("$x")
        # r = request("get", self.base + f"/status/{io}")
        # print("enter", io, r.text)
        # assert r.status_code == 200
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if "clear" in self.finalization: self.clear()
        if "spin_down" in self.finalization: self.spin_down()
        if "stop" in self.finalization: self.stop()

    def spin_down(self):
        c = self.Stop(wait_for_idle=True)
        self.history.append(c)
        c.dispatch(self)
        return c

    def stop(self):
        c = self.Stop(wait_for_idle=False)
        self.history.append(c)
        c.dispatch(self)
        return c

    def and_spin_down(self):
        self.finalization += ("spin_down",)
        return self

    def and_stop(self):
        self.finalization += ("stop",)
        return self


def retry(f, count):
    for i in range(count):
        res = f()
        if res is None: continue
        return res

class ManagedMORK(MORK):
    """
    Wrapper to establish a MORK server connection.  Can connect to a running server or start a server if one isn't already running.
    """
    @classmethod
    def connect(cls, binary_path=None, url=None, *args):
        """
        Connects to a running MORK server, and falls back to starting the server if the connection fails
        """
        try:
            return cls(base_url=url, *args)
        except ConnectionError as e:
            return cls.start(binary_path, *args)

    @classmethod
    def start(cls, binary_path, *args):
        """
        Starts the MORK server.  Fails if it's already running and therefore can't be started

        Args:
            binary_path (str): file system path to the compiled MORK server binary

        Returns:
            Self: a ManagedMORK instance
        """
        print("Starting server from binary")
        bin_hash = b32encode(abs(hash(binary_path)).to_bytes(8)).decode("ascii")
        print("bin hash", bin_hash)
        stdout_path = f"/tmp/.mork_server_stdout_{bin_hash}.log"
        server_stdout = FileIO(stdout_path, "w+")
        stderr_path = f"/tmp/.mork_server_stderr_{bin_hash}.log"
        server_stderr = FileIO(stderr_path, "w+")
        process = Popen([binary_path, *map(str, args)], stdout=server_stdout, stderr=server_stderr)
        print("process id", process.pid)
        sleep(.5)
        if process.returncode is None:  # good, still running
            with open(stdout_path) as f:
                line = f.read()
                address = re.search(r"(https?:\/\/)?((?:(?:25[0-5]|(?:2[0-4]|1\d|[1-9]|)\d)\.?\b){4}):?(\d+)?", line)
            if address is None:
                print("no address in server output", line)
                # sudo ss -ltnup 'sport = :8000'
                # return cls(server_stdout, server_stderr, process)
                raise RuntimeError(f"server failed to start, check logs {stdout_path} and {stderr_path}")
            else:
                protocol, ip, port = address.groups()
                full_address = (protocol or "http://") + ip + ":" + (port or 8000)
                print("server starting at", full_address)
                return cls(server_stdout, server_stderr, process, base_url=full_address)
        else:
            raise RuntimeError(f"server failed to start, check logs {stdout_path} and {stderr_path}")

    def and_log_stdout(self):
        self.finalization += ("log_stdout",)
        return self

    def and_log_stderr(self):
        self.finalization += ("log_stderr",)
        return self

    def and_terminate(self):
        self.finalization += ("terminate",)
        return self

    def cleanup(self):
        if self.process is not None:
            print("sending stop command to server...")
            self.stop()

    def __init__(self, stdout=None, stderr=None, process=None, **kwargs):
        super().__init__(**kwargs)
        self.stdout = stdout
        self.stderr = stderr
        self.process = process

    def __enter__(self):
        # todo poll server status
        return super().__enter__()

    def __exit__(self, exc_type, exc_val, exc_tb):
        super().__exit__(exc_type, exc_val, exc_tb)
        if "log_stdout" in self.finalization:
            # with open(self.stdout) as f:
            #     print("stderr", f.read())
            self.stdout.seek(0)
            print("stdout:", self.stdout.read().decode("utf8"))
        if "log_stderr" in self.finalization:
            # with open(self.stdout) as f:
            #     print("stderr", f.read())
            self.stderr.seek(0)
            print("stderr:", self.stderr.read().decode("utf8"))
        if "terminate" in self.finalization:
            print(exc_type, exc_val, exc_tb, "caused terminate")
            self.cleanup()


def _main():
    with ManagedMORK.start("../target/debug/mork_server").and_log_stdout().and_log_stderr().and_terminate() as server:
        with server.work_at("main").and_clear() as ins:
            print("entered")
            ins.upload("(foo 1)\n(foo 2)\n")
            sleep(1)
            print("data", ins.download_().data)
            sleep(1)
            imp = ins.sexpr_import("https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/simpsons.metta")
            print("imp", imp.response.text)
            sleep(1)
            print("data", ins.download_().data)
            sleep(1)

        print("server data", server.download_().data)
        for i, item in enumerate(server.history):
            print(i, str(item))

if __name__ == '__main__':
    _main()