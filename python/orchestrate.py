from client import MORK
from time import sleep

def _main():
    N = 1024
    T = 8
    with MORK(base_url="http://127.0.0.1:8001") as alice,\
         MORK(base_url="http://127.0.0.1:8002") as bob:

        tasks = []
        for i, participant in enumerate((alice, bob)):
            with participant.work_at("main") as ins:
                ins.clear()
                for core in range(T):
                    Ncore = N//T
                    j = T*i + core
                    r = range(Ncore*j, Ncore*(j+1))
                    print(f"uploading {r} to participant {i} ({j})")
                    ins.upload_("\n".join(f"(ints {core} {k})" for k in r)) # blocking
                for core in range(T):
                    tasks.append(ins.transform((f"(ints {core} $x)", "(ints $core $y)"), (f"(pair {core} $x $y)",))) # non-blocking

        print("dispatched")
        for task in tasks: task.block()
        print("processed")

        for i, participant in enumerate((alice, bob)):
            print(i, participant.download("(main (pair $core $x $y))", "($x x $y)").data.count("\n"))

if __name__ == '__main__':
    # Be sure to fire up the two MORK server instances
    # MORK_SERVER_PORT=8001 target/release/mork-server
    # MORK_SERVER_PORT=8002 target/release/mork-server
    _main()
