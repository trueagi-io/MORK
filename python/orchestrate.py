from client import MORK

def _main():
    with MORK(base_url="http://127.0.0.1:8001") as alice,\
         MORK(base_url="http://127.0.0.1:8002") as bob:

        tasks = []
        for i, participant in enumerate((alice, bob)):
            with participant.work_at("main") as ins, ins.work_at("ints") as ints:
                r = range(1000*i, 1000*(i+1))
                print(f"uploading {r} to {participant} ({i})")
                ints.upload_("\n".join(map(str, r)))
                tasks.append(ints.transform(("$x","$y"), ("(pair $x $y)",)))

        for task in tasks: task.block()
        print("all completed")

        for i, participant in enumerate((alice, bob)):
            print(participant.download("(main (ints (pair $x $y)))", "($x x $y)", max_results=5).data)

        # todo implement more interesting task graph:
        # task graph:
        # upload alice   upload bob
        # process AA     process BB
        # export alice   export bob
        # import bob     import alice
        # process AB     process BA
        # filter         filter
        # download AA,AB download BA,BB


if __name__ == '__main__':
    # Be sure to fire up the two MORK server instances
    # MORK_SERVER_PORT=8001 target/release/mork_server
    # MORK_SERVER_PORT=8002 target/release/mork_server
    _main()