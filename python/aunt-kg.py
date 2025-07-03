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
                    downloaded = src.download("(Individuals $i (Fullname $name))", "$name")
                    print("names", dataset, downloaded.data)

                # Generate isIdDifferent relations so that sister relations aren't reflective
                ids_string = scope.download("(src (Individuals $i (Id $id)))", "$id").data
                ids = [line.strip()[1:-1] for line in ids_string.strip().splitlines() if line.strip()]

                entries = []
                for id0 in ids:
                    for id1 in ids:
                        if id0 != id1:
                            entry = f'(simple (isIdDifferent "{id0}" "{id1}"))'
                            entries.append(entry)
                to_upload = "\n".join(entries)
                scope.upload_(to_upload)

                scope.transform(("(src (Individuals $i (Id $id)))", "(src (Individuals $i (Fullname $name)))"), ("(simple (hasName $id $name))", "(simple (hasId $name $id))")).block()

                scope.transform(("(src (Individuals $i (Id $id)))", "(src (Individuals $i (Sex \"M\")))"), ("(simple (male $id))",)).block()
                scope.transform(("(src (Individuals $i (Id $id)))", "(src (Individuals $i (Sex \"F\")))"), ("(simple (female $id))",)).block()

                scope.transform(("(src (Relations $r (Husband $id)))", "(src (Relations $r (Children $lci $cid)))"), ("(simple (parent $id $cid))",))\
                    .block()
                scope.transform(("(src (Relations $r (Wife $id)))", "(src (Relations $r (Children $lci $cid)))"), ("(simple (parent $id $cid))",)).block()
                scope.transform(("(src (Relations $r (Husband $id)))", "(src (Relations $r (Children $cid)))"), ("(simple (parent $id $cid))",))\
                    .block()
                scope.transform(("(src (Relations $r (Wife $id)))", "(src (Relations $r (Children $cid)))"), ("(simple (parent $id $cid))",)).block()

                scope.transform(("(simple (parent $pid $cid))", "(simple (female $pid))",), ("(simple (mother $pid $cid))",),).block()
                scope.transform(("(simple (mother $pid $cid))", "(simple (hasName $pid $name0))", "(simple (hasName $cid $name1))",), ("(simple (motherByName $name0 $name1))",),).block()

                scope.transform(("(simple (parent $pid $cid0))", "(simple (parent $pid $cid1))", "(simple (isIdDifferent $cid0 $cid1))", "(simple (female $cid0))",), ("(simple (sister $cid0 $cid1))",),).block()
                scope.transform(("(simple (sister $cid0 $cid1))", "(simple (hasName $cid0 $name0))", "(simple (hasName $cid1 $name1))",), ("(simple (sisterByName $name0 $name1))",),).block()

                scope.transform(("(simple (parent $pid $cid))", "(simple (sister $aid $pid))",), ("(simple (aunt $aid $cid))",),).block()
                scope.transform(("(simple (aunt $aid $cid))", "(simple (hasName $aid $name0))", "(simple (hasName $cid $name1))",), ("(simple (auntByName $name0 $name1))",),).block()


    ins.sexpr_export("($dataset (simple $x))", "($dataset $x)", "file://" + __file__.rpartition("/")[0] + "/simple_all.metta")

    for i, item in enumerate(ins.history):
        print("preprocessing event", i, str(item))

def _main():
    with ManagedMORK.connect(binary_path="../target/release/mork_server").and_terminate() as server:
        server.clear().block()
        preprocessing(server)

if __name__ == '__main__':
    _main()
