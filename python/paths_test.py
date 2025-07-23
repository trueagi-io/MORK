from client import MORK, ManagedMORK

def _main():
    payload = "aa\nbb\naaa\nbbc\ncde\n"
    with ManagedMORK.connect(binary_path="../target/debug/mork_server").and_terminate().and_log_stderr().and_log_stdout() as server:
        with server.work_at("c1") as ins:
            ins.upload_(payload)

            t = ins.paths_export_("file://" + __file__.rpartition("/")[0] + "/abc.paths")
            t.block()

    with ManagedMORK.connect(binary_path="../target/debug/mork_server").and_terminate().and_log_stderr().and_log_stdout() as server:
        with server.work_at("c2") as ins:
            t = ins.paths_import_("file://" + __file__.rpartition("/")[0] + "/abc.paths")
            t.block()
            assert ins.download_().data == payload


if __name__ == '__main__':
    _main()
