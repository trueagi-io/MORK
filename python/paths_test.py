from time import sleep
from client import MORK, ManagedMORK

def _main():
    payload = """
(mod 0 0 0)    
(mod 1 1 1)    
(mod 2 0 2)    
(mod 0 1 3)    
(mod 1 0 4)    
(mod 2 1 5)    
(mod 0 0 6)    
"""
    with ManagedMORK.connect(binary_path="../target/debug/mork_server").and_terminate() as server:
        with server.work_at("c1") as ins:
            ins.upload_(payload)

            t = ins.paths_export("(mod $m3 0 $x)", "(mod2 $m3 $x)", "file://" + __file__.rpartition("/")[0] + "/even.paths")
            t.block()


    sleep(1)
    with ManagedMORK.connect(binary_path="../target/debug/mork_server").and_terminate() as server:
        with server.work_at("c2") as ins:
            t = ins.paths_import("(mod2 0 $x)", "(mod6 $x)", "file://" + __file__.rpartition("/")[0] + "/even.paths")
            t.block()
            assert ins.download_().data == "(mod6 0)\n(mod6 6)\n"


if __name__ == '__main__':
    _main()
