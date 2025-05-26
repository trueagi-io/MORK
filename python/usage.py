import unittest

from client import MORK, ManagedMORK
from time import sleep

# class Simple(unittest.TestCase):
#     def test_global_upload_download_identity(self):
#         content = "(foo 1) (foo ())"
#         instance = MORK.at()
#         instance.upload()

class Example(unittest.TestCase):
    def setUp(self):
        self.ins = ManagedMORK.start("../target/debug/mork_server")

    def tearDown(self):
        self.ins.stop()

    def test_auntkg_preprocessing(self):
        with self.ins.work_at("aunt-kg") as ins:
            # datasets = ["royal92", "lordOfTheRings", "adameve", "simpsons"]
            datasets = ["simpsons"]
            for dataset in datasets:
                with ins.work_at(dataset) as scope:
                    scope.sexpr_import(f"https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/{dataset}.metta")
                    sleep(1)

                    downloaded = ins.download("(Individuals $i (Fullname $name))", "$name")
                    print("download", downloaded.data)

                    ins.transform(("(Individuals $i (Id $id))", "(Individuals $i (Fullname $name))"), ("(hasName $id $name)", "(hasId $name $id)"))

                    ins.transform(("(Individuals $i (Id $id))", "(Individuals $i (Sex \"M\"))"), ("(male $id)",))
                    ins.transform(("(Individuals $i (Id $id))", "(Individuals $i (Sex \"F\"))"), ("(female $id)",))

                    father_t = ins.transform(("(Relations $r (Husband $id))", "(Relations $r (Children $lci $cid))"), ("(parent $id $cid)",))
                    # mother_t = father_t.try_when_done(lambda: ins.transform(("(Relations $r (Wife $id))", "(Relations $r (Children $lci $cid))"), ("(parent $id $cid)",)))
                    sleep(1)
                    mother_t = ins.transform(("(Relations $r (Wife $id))", "(Relations $r (Children $lci $cid))"), ("(parent $id $cid)",))
        for i, item in enumerate(ins.history):
            print(i, str(item))
        sleep(1)
        print("data", ins.download_().data)

if __name__ == '__main__':
    # Simple().debug()
    suite = unittest.TestSuite()
    suite.addTest(Example())

    runner = unittest.TextTestRunner()
    runner.run(suite)