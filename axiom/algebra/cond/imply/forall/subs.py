from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(simplify=False)
def apply(given, old, new):
    assert given._has(old)
    assert new.is_symbol
    return ForAll[new:{old}](given._subs(old, new))


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    e_ = Symbol("e'", real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(f(e) > 0, e, e_)
    
    Eq << Eq[-1].simplify()
    

if __name__ == '__main__':
    prove()

