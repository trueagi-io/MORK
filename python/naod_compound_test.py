from client import MORK, ManagedMORK


def main_():
    pattern = ('(name (person josh) $2b97f6df)',
               '(age (person josh) $b69e0438)',
               '(city (person josh) $64309359)',
               '(id (software 1) $d93e156d)',
               '(name (software 1) $e7fab221)',
               '(lang (software 1) $5edcd1fb)',
               '(price (software 1) $3b09c6eb)',
               '(date (created (person josh) (software 1)) $925bcd01)',
               '(weight (created (person josh) (software 1)) $509e0c9a)',
               '(name (person marko) $0376622b)',
               '(age (person marko) $5ecabef9)',
               '(city (person marko) $47d873e1)',
               '(date (created (person marko) (software 1)) $0ae4b0be)',
               '(weight (created (person marko) (software 1)) $3c5cfeee)',
               '(name (person peter) $95d0df7a)',
               '(age (person peter) $fa9e663a)',
               '(city (person peter) $7e447293)',
               '(date (created (person peter) (software 1)) $dc2a3e7b)',
               '(weight (created (person peter) (software 1)) $d9a82236)')

    with ManagedMORK.connect("../target/debug/mork_server").and_log_stdout().and_log_stderr().and_terminate() as server:
        with server.work_at("main") as ins:
            for file in ("created", "software", "person", "knows"):
                ins.sexpr_import_("file://" + __file__.rpartition("/")[0] + "/resources/" + file + ".metta").block()
            ins.query(pattern, project=(), target="(res all_variables {})").block()
            ins.query(pattern, project=(), ortho=True, target="(res (ortho all_variables) {})").block()
            ins.query(pattern, project=("2b97f6df", "d9a82236"), target="(res first_and_last {})").block()
            ins.query(pattern, project=("2b97f6df", "d9a82236"), ortho=True, target="(res (ortho first_and_last) {})").block()
            ins.query(pattern, unit="success", target="(res unit {})").block()
            print("bindings", ins.download("(res $k $i)", "(res $k $i)").data)
            print("bindings", ins.download_().data)


if __name__ == '__main__':
    main_()