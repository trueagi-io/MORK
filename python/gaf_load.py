from time import sleep
from client import MORK, ManagedMORK


def _main():
    paths_file_path = "file:///run/media/adam/14956caa-2539-4de7-bac9-d5d8416f5f11/bio/v5/gaf/edges.metta"

    with ManagedMORK.connect(binary_path="../target/release/mork-server").and_terminate() as server:
        with server.work_at("gaf") as ins:
            ins.sexpr_import_(paths_file_path).block()

            res = ins.explore_()
            print("random samples", res.values())
            print("first 10:")
            for (i, k) in zip(range(10), res.forward()):
                print(i, k)


if __name__ == '__main__':
    _main()
