from client import ManagedMORK

def peano(x): return "Z" if x == 0 else f"(S {peano(x - 1)})"

interpreter = f"""
(exec (process_calculus (IC 0 1 {peano(10)}))
            (, (exec (process_calculus (IC $x $y (S $c))) $sp $st)
                ((step $x) $p $t))
            (, (exec (process_calculus (IC $y $x $c)) $sp $st)
                (exec (process_calculus (R $x)) $p $t)))
((step 0)
    (, (petri (? $channel $payload $body))
        (petri (! $channel $payload)))
    (, (petri $body)))
((step 1)
    (, (petri (| $lprocess $rprocess)))
    (, (petri $lprocess)
        (petri $rprocess)))
"""

petri_dish = f"""
(? (add $ret) ((S $x) $y) (| (! (add (PN $x $y)) ($x $y))
                             (? (PN $x $y) $z (! $ret (S $z)))))
(? (add $ret) (Z $y) (! $ret $y))
(! (add result) ({peano(2)} {peano(2)}))
"""


def _main():
    with ManagedMORK.connect("../target/release/mork-server").and_log_stdout().and_log_stderr().and_terminate() as server:
        with server.work_at("petri") as dish:
            dish.upload_(petri_dish)
        server.upload_(interpreter)
        server.exec(thread_id="process_calculus").block()
        result = server.download("(petri (! result $x))", "$x").data
        print("result", result)
        assert result == f"{peano(4)}\n"

if __name__ == '__main__':
    _main()