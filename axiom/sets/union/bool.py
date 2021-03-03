from sympy import *
from axiom.utility import prove, apply

from axiom import algebre, sets


@apply
def apply(self):
    assert self.is_UNION
    
    return Equality(self, self.func(Piecewise((self.function, self.limits_condition), (self.function.etype.emptySet, True)), *((x,) for x, *_ in self.limits)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    S = Symbol.S(etype=dtype.complex * n)
    x = Symbol.x(complex=True, shape=(n,))
    f = Function.f(etype=dtype.complex * m)
     
    Eq << apply(UNION[x:S](f(x)))
    
    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    prove(__file__)

