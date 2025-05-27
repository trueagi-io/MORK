from typing import Optional
import os
import json
import time
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
    Wrapper for the MORK server-based API.  Used to manage the server connection, or throught the `work_at`
    method to scope activity to a subspace.
    """
    class Request:
        """
        Base class for request to the MORK server
        """
        def __init__(self, method, subdir, **kwargs):
            self.method = method
            self.subdir = subdir
            self.kwargs = kwargs
            self.response = None
            self.error = None
            self.server = None
            self.data = None

        def dispatch(self, server):
            """
            Send a request to the server
            """
            self.server = server
            try:
                self.response = request(self.method, server.base + self.subdir, **self.kwargs)
                if self.response and self.response.status_code == 200:
                    self.data = "ok"

            except (RequestException, ConnectionError) as e:
                self.error = e
                raise e

        def result(self):
            """
            Retrieve the result from a previously dispatched request.

            Returns:
                Any: The result data.
                None: If the result is not yet ready.
            """
            if self.server is None:
                raise RuntimeError(f"Must dispatch a request before it can be polled")
            if self.error is not None:
                raise self.error
            if self.data is not None:
                return self.data
            status_response = request("get", self.server.base + f"/status/{quote(self.status_loc)}", **self.kwargs)
            if status_response and status_response.status_code == 200:
                status_info = json.loads(status_response.text)
                return_status = status_info['status']
                if return_status == "pathForbiddenTemporary":
                    return None
                elif return_status == "pathClear":
                    return "ok"
                else:
                    return return_status #TODO: Add handler for command-specific results

        def poll_for_result(self):
            """
            Continue to poll until a request has returned a result or failed
            """
            while self.result() is None:
                time.sleep(0.005)
            self.data = self.result()
            return self.data

        def __str__(self):
            return str(vars(self))

    class Upload(Request):
        """
        A request to upload the specified data to the server
        """
        #TODO: Specify format
        def __init__(self, pattern, template, data):
            self.pattern = pattern
            self.template = template
            self.data = data
            super().__init__("post", f"/upload/{quote(self.pattern)}/{quote(self.template)}/", data=self.data, headers={"Content-Type": "text/plain"})

    class Download(Request):
        """
        A request to download data from the server
        """
        #TODO: Specify format
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
        """
        A request to clear the items matching `expr`
        """
        def __init__(self, expr):
            self.expr = expr
            super().__init__("get", f"/clear/{quote(self.expr)}/")

    class Stop(Request):
        """
        A request to initiate a server shutdown.

        `wait_for_idle=False` will immediately stop accepting connections, and terminate the server when all
        in-flight activity has stopped.

        `wait_for_idle=True` will will wait to begin the shutdown when the server has been idle for an uninterupted
        time period.
        """
        def __init__(self, wait_for_idle=False):
            self.wait_for_idle = wait_for_idle
            super().__init__("get", f"/stop/" if wait_for_idle else f"/stop/?wait_for_idle")

    class Status(Request):
        """
        A request for the status associated with the expression
        """
        def __init__(self, expr):
            self.expr = expr
            super().__init__("get", f"/status/{quote(expr)}")

        def dispatch(self, server):
            super().dispatch(server)
            if self.response and self.response.status_code == 200:
                self.data = self.response.text

    class Import(Request):
        """
        A request to import data from a file or remotely hosted resource
        """
        #TODO: Specify format
        def __init__(self, pattern, template, file_uri):
            self.pattern = pattern
            self.template = template
            self.uri = file_uri
            self.status_loc = template
            super().__init__("get", f"/import/{quote(self.pattern)}/{quote(self.template)}/?uri={self.uri}")

        def dispatch(self, server):
            super().dispatch(server)
            self.data = None

    class Transform(Request):
        """
        A request to transform `patterns` to `templates`
        """
        def __init__(self, patterns, templates):
            self.patterns = patterns
            self.templates = templates
            self.payload = "(transform (, {}) (, {}))".format(" ".join(patterns), " ".join(templates))
            self.status_loc = templates[0] #GOAT, is there a better location expr to use?
            super().__init__("post", f"/transform_multi_multi/", data=self.payload, headers={"Content-Type": "text/plain"})

        def dispatch(self, server):
            super().dispatch(server)
            self.data = None

    def transform(self, patterns, templates):
        """
        Initiate a transform and return when it is complete
        """
        cmd = self.Transform(tuple(map(self.ns.format, patterns)), tuple(map(self.ns.format, templates)))
        self.history.append(cmd)
        cmd.dispatch(self)
        cmd.poll_for_result()
        return cmd

    def and_clear(self):
        """
        Calling this method will cause the expression subspace to be cleared when exiting the `with` block
        """
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
        """
        Upload `data` to the server
        """
        #TODO: Specify format
        io = self.ns.format("$x")
        cmd = self.Upload("$x", io, data)
        self.history.append(cmd)
        cmd.dispatch(self)
        return cmd

    def download_(self):
        """
        Download everything in the scope
        """
        #TODO: Specify format
        io = self.ns.format("$x")
        cmd = self.Download(io, "$x")
        self.history.append(cmd)
        cmd.dispatch(self)
        return cmd

    def download(self, pattern, template):
        """
        Download items from `pattern` and format them using `template`
        """
        #TODO: Specify format
        io = self.ns.format(pattern)
        cmd = self.Download(io, template)
        self.history.append(cmd)
        cmd.dispatch(self)
        return cmd

    def sexpr_import(self, file_uri):
        """
        Import s-expressions from the specified URI
        """
        io = self.ns.format("$x")
        cmd = self.Import("$x", io, file_uri)
        self.history.append(cmd)
        cmd.dispatch(self)
        cmd.poll_for_result()
        return cmd

    def clear(self):
        """
        Clear the the entire scoped subspace
        """
        io = self.ns.format("$x")
        cmd = self.Clear(io)
        self.history.append(cmd)
        cmd.dispatch(self)
        return cmd

    def work_at(self, name, finalization=(), **kwargs):
        """
        Creates a new scoped subspace to work inside of
        """
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

#GOAT: What is this for?
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
        except (ConnectionError, RequestException) as e:
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
            if self.process is not None:
                self.stdout.seek(0)
                print("stdout:", self.stdout.read().decode("utf8"))
            else:
                print("stdout unavailable with external server")
        if "log_stderr" in self.finalization:
            # with open(self.stdout) as f:
            #     print("stderr", f.read())
            if self.process is not None:
                self.stderr.seek(0)
                print("stderr:", self.stderr.read().decode("utf8"))
            else:
                print("stderr unavailable with external server")
        if "terminate" in self.finalization:
            print(exc_type, exc_val, exc_tb, "caused terminate")
            self.cleanup()


def _main():
    with ManagedMORK.connect("../target/debug/mork_server").and_log_stdout().and_log_stderr().and_terminate() as server:
        with server.work_at("main").and_clear() as ins:
            print("entered")
            ins.upload("(foo 1)\n(foo 2)\n")

            print("data", ins.download_().data)

            imp = ins.sexpr_import("https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/simpsons.metta")
            print("imp", imp.response.text)

            print("data", ins.download_().data)

        print("server data", server.download_().data)
        for i, item in enumerate(server.history):
            print(i, str(item))

if __name__ == '__main__':
    _main()