from client import MORK, ManagedMORK

def show_all(ins):
    print(ins.download_().data)

def get_address(ins):
    print("result: ", ins.download("(Head (Source (Corporation (Address $addr))))", "(Got Addr $addr)").data)

def _main():
    with ManagedMORK.connect(binary_path="../target/release/mork-server").and_terminate() as server:
        server.clear().block() # for the example, make sure we have a clear workspace
        server.paths_import_("file://" + __file__.rpartition("/")[0] + "/resources/pobox.paths")
        show_all(server)
        get_address(server)

if __name__ == '__main__':
    _main()
