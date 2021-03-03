from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(ceil):
    divide = axiom.is_Ceiling(ceil)
    n, d = axiom.is_Divide(divide)

    return Equality(ceil, (n + d - 1) // d)


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True, positive=True)
    Eq << apply(ceiling(n / d))
    
    Eq << Eq[-1].this.lhs.apply(algebre.ceiling.astype.times)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1] + (-n // d - 1)
    
    Eq << Eq[-1].reversed
    
    Eq << (-n % d).this.definition
    
    Eq << ((d + n - 1) % d).this.definition
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq << Eq[-1] / d
    
    Eq << Eq[-1] - 1

    
if __name__ == '__main__':
    prove(__file__)