from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    assert self.is_Bool
    return Equal(self, Piecewise((1, self.arg), (0, True)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
     
    Eq << apply(Bool(x > y))
    
    Eq << Eq[0].this.lhs.definition


if __name__ == '__main__':
    prove()

