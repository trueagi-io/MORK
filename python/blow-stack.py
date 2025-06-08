from client import MORK, ManagedMORK

def space_query_fatality_combo(depth, width):
    def rec(d, i, buf, last):
        if d == depth:
            buf += f"$y" if last else f"v{d}_{i}"
        else:
            buf += "("
            for i in range(width):
                if i != 0: buf += " "
                rec(d + 1, i, buf, last and (i == (width - 1)))
            buf += ")"

    space_e, query_e = [], []
    rec(0, 1, space_e, False)
    rec(0, 1, query_e, True)
    return f"(X {''.join(space_e)})", f"($x {''.join(query_e)})"

def _main():
    space, query = space_query_fatality_combo(3, 10)
    print("space", space)
    print("query", query)
    with ManagedMORK.start(binary_path="../target/release/mork_server").and_terminate() as server:
        with server.work_at("boom") as ins:
            ins.upload_(space)

            t = ins.transform((query,), ("(both $x $y)",))
            t.block()
            print(t)


if __name__ == '__main__':
    _main()
