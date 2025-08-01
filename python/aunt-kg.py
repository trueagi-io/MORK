from functools import partial
from multiprocessing import Pool, cpu_count
from client import MORK, ManagedMORK


DATASETS = (
    "royal92",
    "lordOfTheRings",
    "adameve",
    "simpsons",
)

def preprocessing(server, datasets=DATASETS):
    with server.work_at("aunt-kg") as ins:
        for dataset in datasets:
            with ins.work_at(dataset) as scope:
                with scope.work_at("src") as src:
                    src.sexpr_import_(f"https://raw.githubusercontent.com/Adam-Vandervorst/metta-examples/refs/heads/main/aunt-kg/{dataset}.metta")\
                        .block()
                    # test: see the names of the people in the dataset
                    downloaded = src.download("(Individuals $i (Fullname $name))", "$name", max_results=5)
                    print("5 names", dataset, downloaded.data)

                scope.transform(("(src (Individuals $i (Id $id)))", "(src (Individuals $i (Fullname $name)))"),
                                ("(simple (hasName $id $name))", "(simple (hasId $name $id))")).block()

                scope.transform(("(src (Individuals $i (Id $id)))", "(src (Individuals $i (Sex \"M\")))"),
                                ("(simple (male $id))",)).block()
                scope.transform(("(src (Individuals $i (Id $id)))", "(src (Individuals $i (Sex \"F\")))"),
                                ("(simple (female $id))",)).block()

                scope.transform(("(src (Relations $r (Husband $id)))", "(src (Relations $r (Children $lci $cid)))"),
                                ("(simple (parent $id $cid))",)).block()
                scope.transform(("(src (Relations $r (Wife $id)))", "(src (Relations $r (Children $lci $cid)))"),
                                ("(simple (parent $id $cid))",)).block()
                # Agh, overloading of keys in JSON, see https://github.com/trueagi-io/MORK/pull/11
                scope.transform(("(src (Relations $r (Husband $id)))", "(src (Relations $r (Children $cid)))"),
                                ("(simple (parent $id $cid))",)).block()
                scope.transform(("(src (Relations $r (Wife $id)))", "(src (Relations $r (Children $cid)))"),
                                ("(simple (parent $id $cid))",)).block()


        path = "file://" + __file__.rpartition("/")[0] + "/simple_all.metta"
        ins.sexpr_export("($dataset (simple $x))", "($dataset $x)", path).block()

    # test: see the steps performed by the server
    # for i, item in enumerate(ins.history):
    #     print("preprocessing event", i, str(item))


def is_different_hack(scope, ids, leave_out_id):
    # note that `leave_out_id` is a prefix and thread-specific, hence allowed to happen in parallel
    with scope.work_at(namespace=f'(simple (isIdDifferent "{leave_out_id}" "{{}}"))') as private_ns:
        private_ns.upload_("\n".join(id0 for id0 in ids if id0 != leave_out_id))

def hack(server, datasets=DATASETS, parallel=True):
    # HACK: Generate isIdDifferent relations so that sister relations aren't reflective
    if parallel: pool = Pool(cpu_count()//2)
    with server.work_at("aunt-kg") as ins:
        for dataset in datasets:
            with ins.work_at(dataset) as scope:
                ids_string = scope.download("(src (Individuals $i (Id $id)))", "$id").data
                ids = [line.strip()[1:-1] for line in ids_string.strip().splitlines() if line]
                if parallel: pool.map(partial(is_different_hack, scope._bare(), ids), ids)
                else: scope.upload_("".join(f'(simple (isIdDifferent "{leave_out_id}" "{id0}"))\n'
                                            for id0 in ids for leave_out_id in ids if id0 != leave_out_id))
    if parallel: pool.terminate()

def processing(server, datasets=DATASETS, human_readable=True):
    with server.work_at("aunt-kg") as ins:
        for dataset in datasets:
            with ins.work_at(dataset).work_at("simple").and_time() as scope:
                scope.transform(("(parent $pid $cid)", "(female $pid)",),
                                ("(mother $pid $cid)",),).block()
                if human_readable: scope.transform(("(mother $pid $cid)", "(hasName $pid $name0)", "(hasName $cid $name1)",), ("(motherByName $name0 $name1)",),).block()

                scope.transform(("(parent $pid $cid0)", "(parent $pid $cid1)", "(isIdDifferent $cid0 $cid1)", "(female $cid0)",),
                                ("(sister $cid0 $cid1)",),).block()
                if human_readable: scope.transform(("(sister $cid0 $cid1)", "(hasName $cid0 $name0)", "(hasName $cid1 $name1)",), ("(sisterByName $name0 $name1)",),).block()

                scope.transform(("(parent $pid $cid)", "(sister $aid $pid)",),
                                ("(aunt $aid $cid)",),).block()
                if human_readable: scope.transform(("(aunt $aid $cid)", "(hasName $aid $name0)", "(hasName $cid $name1)",), ("(auntByName $name0 $name1)",),).block()

def _main():
    with ManagedMORK.connect(binary_path="../target/release/mork_server").and_terminate() as server:
        server.clear().block()
        preprocessing(server)
        hack(server, parallel=True)
        processing(server, human_readable=False)

if __name__ == '__main__':
    _main()
