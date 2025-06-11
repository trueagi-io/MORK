from client import MORK, ManagedMORK

def _main():
    with ManagedMORK.connect(binary_path="../target/release/mork_server").and_terminate() as server:
        with server.work_at("toy") as ins:
            ins.upload_("\n".join(str(i) for i in range(10000)))

        res = server.explore_()

        print([c for _, c in zip(range(300), res.forward())])
        print([c for _, c in zip(range(300), res.backward())])

        for i, level in zip(range(5), res.levels()):
            print("level", i)
            for c in level:
                print(" ", c.values())

if __name__ == '__main__':
    _main()
