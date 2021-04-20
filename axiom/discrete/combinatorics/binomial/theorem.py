from sympy import *
from axiom.utility import prove, apply

from axiom.discrete.combinatorics.binomial import Pascal
from axiom import algebra


@apply
def apply(x, y, n=None, free_symbol=None):
    if free_symbol is None:
        k = Symbol.k(integer=True)
    else:
        k = free_symbol
    if n is None:
        n = Symbol.n(integer=True, nonnegative=True)
        return Equal((x + y) ** n, Sum[k:0:n + 1](binomial(n, k) * x ** k * y ** (n - k)))
    elif n < 0:
        return
    else:
        return Equal((x + y) ** n, Sum[k:0:n + 1](binomial(n, k) * x ** k * y ** (n - k)))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    n = Symbol.n(integer=True, nonnegative=True, given=False)
    Eq << apply(x, y, n)

    Eq.induction = Eq[-1].subs(n, n + 1)

    Eq << Eq[-1] * (x + y)
    
    Eq << Eq[-1].this.lhs.powsimp()

    Eq << Eq[-1].this.rhs.astype(Sum)
    
    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq[-1].this.rhs.function.powsimp()
    
    (k, *_), *_ = Eq[-1].rhs.limits
    Eq << Eq[-1].this.rhs.astype(Add)
    
    Eq << Eq[-1].this.rhs.args[1].limits_subs(k, k - 1)
    
    Eq << Eq.induction.subs(Pascal.apply(n + 1, k))
    
    Eq << Eq[-1].this.rhs.astype(Add)
    
    Eq << Eq[-1].this.rhs.args[0].simplify()
    
    Eq << Eq[-1].this.rhs.args[1].simplify()
    
    Eq << Eq.induction.induct()
    
    Eq << algebra.sufficient.imply.cond.induction.apply(Eq[-1], n=n)


if __name__ == '__main__':
    prove()

