from axiom.utility import prove, apply
from sympy import *
import axiom


@apply
def apply(self):
    n = axiom.is_Factorial(self)
    assert n > 0
    return Equal(self, n * factorial(n - 1))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(factorial(n))
    
    Eq << Eq[0].this.find(factorial).definition
    
    Eq << Eq[-1].this.find(factorial).definition
    
    Eq << Eq[-1].this.lhs.bisect({n})


if __name__ == '__main__':
    prove()
