class Module:
    def __init__(self, prefix="", postfix=""):
        self.pre = prefix
        self.post = postfix
    def __getitem__(self, name):
        return Module(f"({name} " + self.pre, self.post + ")")
    def __call__(self, *args, **kwargs):
        print(self.pre, **kwargs, end="")
        print(*args, **kwargs, end="")
        print(self.post, **kwargs, end="\n")

N_TUPLES = 22

def get(m: Module):
    for n in range(N_TUPLES+1):
        for k in range(n):
            m(f"(get ({' '.join(f'$x{i}' for i in range(n))}) {k} $x{k})")

if __name__ == '__main__':
    root = Module()
    std = root['std']
    get(std)
