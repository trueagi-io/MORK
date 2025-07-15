from datetime import datetime
from typing import Optional
import os
import json
import time
from time import monotonic, sleep
from base64 import b32encode
import re
from io import StringIO, FileIO
from urllib.parse import quote, quote_from_bytes

import requests
from requests import request, RequestException
from requests_sse import EventSource, InvalidStatusCodeError, InvalidContentTypeError
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
            except (RequestException, ConnectionError) as e:
                self.error = e
                raise e

        def poll(self):
            """
            Poll the status path.

            Returns:
                (finished: bool, metadata: Any)
            """
            if self.server is None:
                raise RuntimeError(f"Must dispatch a request before it can be polled")

            # status_loc == subdir  or  status_loc == unique_id
            status_response = request("get", self.server.base + f"/status/{quote(self.status_loc)}", **self.kwargs)
            print("poll status: ", status_response.text)
            if status_response and status_response.status_code == 200:
                status_info = json.loads(status_response.text)
                return_status = status_info['status']
                if return_status == "pathForbiddenTemporary":
                    return (False, "")
                elif return_status == "pathClear":
                    return (True, "")
                else:
                    return (True, status_info)
            # http error
            status_info = {'httpErr': status_response}
            return (True, status_info)

        def block(self, delay=0.005, base=2, max_attempts=16):
            """
            Continue to poll until a request has returned a result or failed

            Polls according to delay*base^attempt for attempt < max_attempts (else raises StopIteration)

            Returns:
                metadata: Any
            """
            is_finished, meta = self.poll()
            attempt = 1
            while not is_finished:
                time.sleep(delay*base**attempt)
                is_finished, meta = self.poll()
                attempt += 1
                if attempt > max_attempts:
                    raise StopIteration
            return meta

        def listen(self, timeout: Optional[float] = 300):
            """
            Listens to server-side events on the status of a request.

            Yields:
                dict[str, Any]: Parsed JSON messages from the event stream.
            """
            url = self.server.base + f"/status_stream/{quote(self.status_loc)}"
            with EventSource(url, timeout=timeout) as event_source:
                for event in event_source:
                    if event.data:
                        msg = json.loads(event.data)
                        yield msg

            print("event stream closed")

        def listen_until_clear(self, timeout: Optional[float] = 300):
            """
            Listens to server side events until a 'pathClear' status is received.

            Args:
                timeout (float): The maximum amount of time to listen.

            Returns:
                metadata: Any

            Raises:
                TimeoutError: If the timeout is reached before the path is clear.
            """
            start_time = monotonic()
            
            try:
                for msg in self.listen(timeout=timeout):
                    if timeout and (monotonic() - start_time) > timeout:
                        raise TimeoutError(f"listen_until_clear timed out after {timeout} seconds")

                    status = msg.get("status")
                    if status == "pathClear":
                        return ""
                    elif status == "pathForbiddenTemporary":
                        continue
                    else:
                        return msg
            except requests.exceptions.ReadTimeout:  # timeout raised by requests module
                raise TimeoutError(f"Timeout of {timeout}s waiting for event from server.") from None
            except Exception as e:  # unkown exceptions
                print(f"An unexpected error occurred: {e}")
                raise


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

        def poll(self):
            return (True, "upload already blocks")

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
            # print("download status code:", self.response.status_code)
            if self.response and self.response.status_code == 200:
                self.data = self.response.text

        def poll(self):
            return (True, "download already blocks")

    class Clear(Request):
        """
        A request to clear the items matching `expr`
        """
        def __init__(self, expr):
            self.expr = expr
            self.status_loc = expr
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

        def poll(self):
            is_finished, result = super().poll()
            # All non-empty results from `import` are errors
            if is_finished and result != "":
                if 'httpErr' in result:
                    raise ConnectionError(result)
                raise RuntimeError(result)
            return (is_finished, result)

    class Export(Request):
        """
        A request to export data to a file
        """
        #TODO: Specify format
        def __init__(self, pattern, template, file_uri):
            self.pattern = pattern
            self.template = template
            self.status_loc = template
            self.uri = file_uri
            super().__init__("get", f"/export/{quote(self.pattern)}/{quote(self.template)}/?uri={self.uri}")

    class Transform(Request):
        """
        A request to transform `patterns` to `templates`
        """
        def __init__(self, patterns, templates):
            self.patterns = patterns
            self.templates = templates
            self.payload = "(transform (, {}) (, {}))".format(" ".join(patterns), " ".join(templates))
            self.status_loc = templates[0] #GOAT, is there a better location expr to use?
            super().__init__("post", f"/transform/", data=self.payload, headers={"Content-Type": "text/plain"})

    class Explore(Request):
        def __init__(self, pattern, token=""):
            self.pattern = pattern
            super().__init__("get", f"/explore/{quote(self.pattern)}/{token}/")

        def dispatch(self, server):
            super().dispatch(server)
            if self.response and self.response.status_code == 200:
                self.data = json.loads(self.response.text)

        def values(self):
            return [d["expr"] for d in self.data]

        def descend(self, i):
            return type(self)(self.pattern, quote_from_bytes(bytes(self.data[i]["token"])))

        def _children(self):
            for d in self.data:
                yield type(self)(self.pattern, quote_from_bytes(bytes(d["token"])))

        def levels(self):

            frontier = [self]
            while True:
                for c in frontier:
                    c.dispatch(self.server)
                yield frontier
                frontier = [child for c in frontier for child in c._children()]
                if not frontier:
                    break

        def forward(self):
            # still buggy
            children = self._children()
            values = self.values()

            def traverse(n):
                n.dispatch(self.server)
                n_children = n._children()
                n_values = n.values()

                for n_idx, n_child in enumerate(n_children):
                    if n_idx > 0: yield n_values[n_idx]
                    yield from traverse(n_child)

            for value, child in zip(values, children):
                yield value
                yield from traverse(child)

        def backward(self):
            # still buggy
            children = list(self._children())
            values = self.values()

            def traverse(n):
                n.dispatch(self.server)
                n_children = list(n._children())
                n_values = n.values()
                for n_idx, n_child in enumerate(reversed(n_children)):
                    yield from traverse(n_child)
                    yield n_values[-n_idx - 1]

            for value, child in zip(reversed(values), reversed(children)):
                yield from traverse(child)
                yield value

    class Exec(Request):
        def __init__(self, location=None):
            if location: self.status_loc = f"(exec {location})"
            super().__init__("get", f"/metta_thread/" if location is None else f"/metta_thread/?location={location}")

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

    def transform(self, patterns, templates):
        """
        Initiate a transform
        """
        cmd = self.Transform(tuple(map(self.ns.format, patterns)), tuple(map(self.ns.format, templates)))
        self.history.append(cmd)
        cmd.dispatch(self)
        return cmd

    def upload_(self, data):
        """
        Upload `data` to the scope
        """
        #TODO: Specify format
        return self.upload("$x", "$x", data)

    def upload(self, pattern, template, data):
        """
        Upload `data` matching `pattern` to the server formatted in `template`
        """
        #TODO: Specify format
        io = self.ns.format(template)
        cmd = self.Upload(pattern, io, data)
        self.history.append(cmd)
        cmd.dispatch(self)
        return cmd

    def download_(self):
        """
        Download everything in the scope
        """
        return self.download("$x", "$x")

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

    def sexpr_export_(self, file_uri):
        return self.sexpr_export("$x", "$x", file_uri)

    def sexpr_export(self, pattern, template, file_uri):
        """
        Export items from `pattern` in the space and format them in `file` using `template`
        """
        io = self.ns.format(pattern)
        cmd = self.Export(io, template, file_uri)
        self.history.append(cmd)
        cmd.dispatch(self)
        return cmd

    def sexpr_import_(self, file_uri):
        return self.sexpr_import("$x", "$x", file_uri)

    def sexpr_import(self, pattern, template, file_uri):
        """
        Import s-expressions from the specified URI match `pattern` into `template`
        """
        io = self.ns.format(template)
        cmd = self.Import(pattern, io, file_uri)
        self.history.append(cmd)
        cmd.dispatch(self)
        return cmd

    def clear(self):
        """
        Clear the entire scoped subspace
        """
        io = self.ns.format("$x")
        cmd = self.Clear(io)
        self.history.append(cmd)
        cmd.dispatch(self)
        return cmd

    def explore_(self):
        io = self.ns.format("$x")
        cmd = self.Explore(io)
        self.history.append(cmd)
        cmd.dispatch(self)
        return cmd

    def exec(self, thread_id="*"):
        """
        Execute MM2
        """
        cmd = self.Exec(self.ns.format(thread_id))
        self.history.append(cmd)
        cmd.dispatch(self)
        return cmd

    def work_at(self, name, finalization=(), **kwargs):
        """
        Creates a new scoped subspace to work inside of
        """
        return MORK(**kwargs, namespace=self.ns.format(f"({name} {{}})"), finalization=finalization, parent=self, history=self.history)

    def __enter__(self):
        # io = self.ns.format("$x")
        # r = request("get", self.base + f"/status/{io}")
        # print("enter", io, r.text)
        # assert r.status_code == 200
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if "time" in self.finalization: print(f"{self.ns.format("*")} time {monotonic() - self.t0:.6f} s")
        if "clear" in self.finalization: self.clear().listen_until_clear()
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

    def and_clear(self):
        """
        Calling this method will cause the expression subspace to be cleared when exiting the `with` block
        """
        self.finalization += ("clear",)
        return self

    def and_time(self):
        self.t0 = monotonic()
        self.finalization += ("time",)
        return self

    def _bare(self) -> 'MORK':
        return _BareMORK(self.base, self.ns)

class _BareMORK(MORK):
    def __init__(self, base, ns):
        self.base = base
        self.ns = ns
        self.history = []

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
        if not os.path.isfile(binary_path):
            raise RuntimeError(f"Can't connect to running server, and no server binary found at path: {binary_path}")

        print("Starting server from binary")
        bin_hash = b32encode(abs(hash(binary_path)).to_bytes(8)).decode("ascii")
        print("bin hash", bin_hash)
        stdout_path = f"/tmp/.mork_server_stdout_{bin_hash}.log"
        server_stdout = FileIO(stdout_path, "w+")
        stderr_path = f"/tmp/.mork_server_stderr_{bin_hash}.log"
        server_stderr = FileIO(stderr_path, "w+")
        process = Popen([binary_path, *map(str, args)], stdout=server_stdout, stderr=server_stderr, env={"RUST_BACKTRACE": "1"})
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
            if exc_type is None:
                print("normal termination")
            else:
                print(exc_type, exc_val, exc_tb, "caused terminate")
            self.cleanup()


def _main():
    # smoke test
    with ManagedMORK.connect("../target/debug/mork_server").and_log_stdout().and_log_stderr().and_terminate() as server:
        with server.work_at("main").and_clear() as ins:
            print("entered")
            ins.upload_("(foo 1)\n(foo 2)\n")

            print("data", ins.download_().data)

            ins.sexpr_import_("https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/simpsons.metta").listen_until_clear()

            print("data", ins.download_().data)

        print("server data", server.download_().data)
        for i, item in enumerate(server.history):
            print(i, str(item))

def _main_mm2():
    # smoke test
    with ManagedMORK.connect("../target/debug/mork_server").and_log_stdout().and_log_stderr().and_terminate() as server:
        server.upload_("(data (foo 1))\n(data (foo 2))\n(_exec 0 (, (data (foo $x))) (, (data (bar $x))))")
        server.transform(("(_exec $priority $p $t)",), ("(exec (test $priority) $p $t)",)).listen_until_clear(5)
        server.exec(thread_id="test").listen_until_clear(5)
        # print("data", server.download_().data)
        #
        # for i, item in enumerate(server.history):
        #     print(i, str(item))

def _test_sse_status():
    with ManagedMORK.connect("../target/debug/mork_server").and_log_stdout().and_log_stderr().and_terminate() as server:
        DATASETS = (
            "royal92",
            "lordOfTheRings",
            "adameve",
            "simpsons",
        )
        for dataset in DATASETS:
            server.sexpr_import_(
                f"https://raw.githubusercontent.com/Adam-Vandervorst/metta-examples/refs/heads/main/aunt-kg/{dataset}.metta"
            ).listen_until_clear()



if __name__ == '__main__':
    # _main()
    _main_mm2()




