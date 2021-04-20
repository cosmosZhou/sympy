from sympy import *
from axiom.utility import prove, apply
import axiom
# given: x != y
# x not in {y}


@apply
def apply(given):
    x, S = axiom.is_Contains(given)
    return Unequal(S, x.emptySet)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)
    S = Symbol.S(etype=dtype.complex * n, given=True)
    Eq << apply(Contains(x, S))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[0].subs(Eq[-1])
        

if __name__ == '__main__':
    prove()

