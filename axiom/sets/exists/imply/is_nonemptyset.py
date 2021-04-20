from sympy import *
from axiom.utility import prove, apply
from axiom import algebra


@apply
def apply(given):
    assert given.is_Exists
    assert len(given.limits) == 1
    x, S = given.limits[0]
    return Unequal(S, x.emptySet)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(Exists[e:S](f(e) > 0))
    
    Eq << Exists[e:S](Contains(e, S) & Eq[0].function, plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << algebra.exists_et.imply.exists.split.apply(Eq[-1])
        

    
if __name__ == '__main__':
    prove()

