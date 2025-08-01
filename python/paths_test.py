from time import sleep
from client import MORK, ManagedMORK


def _main(synthetic=None):
    if isinstance(synthetic, int):
        payload = "\n".join(f"(mod {i % 3} {i % 2} {i})" for i in range(synthetic))
    else:
        payload = """
(mod 0 0 0)    
(mod 1 1 1)    
(mod 2 0 2)    
(mod 0 1 3)    
(mod 1 0 4)    
(mod 2 1 5)    
(mod 0 0 6)    
"""

    # we're going from an in-memory space, to a serialized file, and back to an in-memory space
    # Going to the file, we're only serializing values 0 mod 2, and going to the space, we're only serializing values 0 mod 3
    # Thus, the final in-memory space contains only values dividable by 6
    binary_path = "../mork_server"
    paths_file_path = "file://" + __file__.rpartition("/")[0] + "/even.paths"

    with ManagedMORK.connect(binary_path).and_terminate() as server:
        with server.work_at("c1") as ins:
            ins.upload_(payload)

            ins.paths_export("(mod $m3 0 $x)", "(mod2 $m3 $x)", paths_file_path).block()

    sleep(1)
    with ManagedMORK.connect(binary_path).and_terminate() as server:
        with server.work_at("c2") as ins:
            ins.paths_import("(mod2 0 $x)", "(mod6 $x)", paths_file_path).block()

            if isinstance(synthetic, int):
                assert ins.download_().data.strip() == "\n".join(f"(mod6 {i})" for i in range(synthetic) if i % 6 == 0)
            else:
                assert ins.download_().data == "(mod6 0)\n(mod6 6)\n"


if __name__ == '__main__':
    _main()
