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

                scope.transform(("(src (Individuals $i (Id $id)))", "(src (Individuals $i (Fullname $name)))"), ("(simple (hasName $id $name))", "(simple (hasId $name $id))"))

                scope.transform(("(src (Individuals $i (Id $id)))", "(src (Individuals $i (Sex \"M\")))"), ("(simple (male $id))",))
                scope.transform(("(src (Individuals $i (Id $id)))", "(src (Individuals $i (Sex \"F\")))"), ("(simple (female $id))",))

                scope.transform(("(src (Relations $r (Husband $id)))", "(src (Relations $r (Children $lci $cid)))"), ("(simple (parent $id $cid))",))\
                    .block()
                scope.transform(("(src (Relations $r (Wife $id)))", "(src (Relations $r (Children $lci $cid)))"), ("(simple (parent $id $cid))",))

    ins.sexpr_export("($dataset (simple $x))", "($dataset $x)", "file://" + __file__.rpartition("/")[0] + "/simple_all.metta")

    for i, item in enumerate(ins.history):
        print("preprocessing event", i, str(item))

def _main():
    with ManagedMORK.connect(binary_path="../target/release/mork_server").and_terminate() as server:
        server.clear().block()
        preprocessing(server)

if __name__ == '__main__':
    _main()
