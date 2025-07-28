from collections import defaultdict
from random import random


class Variable:
    all: 'list[Variable]' = []
    def __init__(self, name, formula, stv):
        self.name = name
        self.formula = formula
        self.stv = stv
        self.to_factors = []
        self.__class__.all.append(self)

    def __hash__(self):
        return hash(self.name)

class Factor:
    all: 'list[Factor]' = []
    def __init__(self, name, combined_potential):
        self.name = name
        self.combined_potential = combined_potential
        self.to_variables = []
        self.__class__.all.append(self)

    def __hash__(self):
        return hash(self.name)

def link(v: Variable, f: Factor):
    v.to_factors.append(f)
    f.to_variables.append(v)

def mul_stv(x, y):
    (s1, c1) = x
    (s2, c2) = y
    return s1*s2 , 1. - (1. - c1)*(1. - c2)

def add_stv(x, y):
    (s1, c1) = x
    (s2, c2) = y
    return s1 + s2 - s1*s2, c1 + c2 - c1*c2

def add_all_stv(xs):
    z = (0., 0.)
    for x in xs: z = add_stv(z, x)
    return z

def logic_join(x, y):
    return f"({x} | {y})"

def logic_meet(x, y):
    return f"({x} & {y})"

BOTTOM = ("false", (0.,0.))
UNIT = ("true", (0.,0.))

def join(x, y):
    ɸ1, ɑ1 = x
    ɸ2, ɑ2 = y
    return logic_join(ɸ1, ɸ2), add_stv(ɑ1, ɑ2)

def join_all(xs):
    z = BOTTOM
    for x in xs: z = join(x, z)
    return z

def mul(x, y):
    ɸ1, ɑ1 = x
    ɸ2, ɑ2 = y
    return logic_meet(ɸ1, ɸ2), mul_stv(ɑ1, ɑ2)

def mul_all(xs):
    z = UNIT
    for x in xs: z = mul(x, z)
    return z

def random_stv():
    return random(), random()

def DeductionSTV(stv):
    (s, c) = stv
    return .8*s, .8*c

def phi_ded(x):
    ɸ, ɑ = x
    if "Dog" in ɸ: # a heavy stand-in...
        return ɸ.replace("Dog", "Mammal"), DeductionSTV(ɑ)

def quantify(vs, f):
    print("quantify", {v.name for v in vs}, f)
    # This is closer to what I'd have expected, but produces the wrong result
    # return "(" + " | ".join(f.replace("x", v.formula) for v in vs) + ")"  # a heavy stand-in...
    return f

def silly():
    vDog = Variable("vDog", "Dog(Lassie)", (0.9, 0.9))
    vMammal = Variable("vMammal", "Mammal(Lassie)", (0.0,0.0))
    fDed = Factor("fDed", phi_ded)
    link(vDog, fDed)
    link(vMammal, fDed)

    varToFac = defaultdict(dict)
    facToVar = defaultdict(dict)
    def round():
        nonlocal varToFac
        for v in Variable.all:
            for f in v.to_factors:
                other_f = set(v.to_factors) - {f}
                addition = join_all(other_f)
                old_v = (v.formula, v.stv)
                new_v = join(old_v, addition)
                varToFac[v][f] = new_v
                print(f"m_{{{v.name}->{f.name}}} = {new_v}")
        nonlocal facToVar
        for f in Factor.all:
            for v in f.to_variables:
                other_v = set(f.to_variables) - {v}
                m_potential = f.combined_potential(mul_all(varToFac[v_][f] for v_ in other_v))
                if m_potential is None:
                    print(f"skipping {f.name}->{v.name}")
                    continue
                (new_formula, new_stv) = m_potential
                # I expected add_all_stv(v_.stv for v_ in other_v) instead of new_stv
                new_v = (quantify(other_v, new_formula), new_stv)
                facToVar[f][v] = new_v
                print(f"m_{{{f.name}->{v.name}}} = {new_v}")

    def marginal(v):
        return join_all(facToVar[f][v] for f in v.to_factors)

    round()
    print("marginal", marginal(vMammal))

if __name__ == '__main__':
    silly()
    # x = random_stv()
    # y = random_stv()
    # z = random_stv()
    # print(x, y, z)
    # print(mul_stv(x, y), mul_stv(y, z), mul_stv(mul_stv(x, y), z), mul_stv(x, mul_stv(y, z)))
    # print(add_stv(x, y), add_stv(y, z), add_stv(add_stv(x, y), z), add_stv(x, add_stv(y, z)))


# Var -> Fac
# (Message (Var $v) (Fac $f) <update>)
# <update> = join_all($m)  (Nbr (Var $v) $f_) (diff $f $f_) (Message (Fac $f_) (Var $v) $m)
# Fac -> Var
# (Message (Fac $f) (Var $v) <update>)
# <update> = marginalize($vf) (V $f $vf) (diff $vf $v) <factor>
# <factor> = (phi $f $phif) $phif * prod_all($m) (Nbr $f (Var $v_)) (diff $v $v_) (Message (Var $v_) (Fac $f) $m)
