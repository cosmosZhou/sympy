from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets


@apply
def apply(self):
    assert self.is_Product
    
    return Equal(self, self.func(self.function ** Bool(self.limits_cond), *((x,) for x, *_ in self.limits)))


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.integer)
    x = Symbol.x(integer=True)
    f = Function.f(real=True)
     
    Eq << apply(Product[x:S](f(x)))
    
    Eq << Eq[0].this.rhs.function.args[1].definition
    
    Eq << Eq[-1].this.rhs.function.astype(Piecewise)


if __name__ == '__main__':
    prove()

