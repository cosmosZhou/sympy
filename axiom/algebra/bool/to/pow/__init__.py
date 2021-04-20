from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self, n=None):
    assert self.is_Bool
    assert n.is_integer
    assert n > 0
    return Equal(self, self ** n)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    n = Symbol.n(integer=True, positive=True, given=False)
     
    Eq << apply(Bool(x > y), n)
    
    Eq.induct = Eq[0].subs(n, n + 1)
    
    Eq << Eq[0] * Bool(x > y)
    
    Eq << Eq[-1].this.lhs.apply(algebra.pow.to.bool)
    
    Eq << Eq[-1].this.rhs.powsimp()
    
    Eq << Eq.induct.induct()

    Eq << algebra.sufficient.imply.cond.induction.apply(Eq[-1], n=n, start=1)

if __name__ == '__main__':
    prove()

from . import square
