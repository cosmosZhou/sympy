
from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy import Symbol
from axiom.discrete.combinatorics.binomial import Pascal
from sympy.concrete.summations import Sum
from sympy.core.add import Plus
from axiom import algebre

@plausible
def apply(x, y, n=None, free_symbol=None):
    if free_symbol is None:
        k = Symbol.k(integer=True)
    else:
        k = free_symbol
    if n is None:
        n = Symbol.n(integer=True, nonnegative=True)
        return Equality((x + y) ** n, Sum[k:0:n](binomial(n, k) * x ** k * y ** (n - k)))
    elif n < 0:
        return None
    else:
        return Equality((x + y) ** n, Sum[k:0:n](binomial(n, k) * x ** k * y ** (n - k)))


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(x, y, n)

    Eq.induction = Eq[-1].subs(n, n + 1)

    Eq << (Eq[-1] * (x + y)).powsimp()

#     Eq << Eq[-1].subs(Eq.induction)

    Eq << Eq[-1].this.rhs.astype(Sum)
    
    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq[-1].this.rhs.function.powsimp()
    
    (k, *_), *_ = Eq[-1].rhs.limits
    Eq << Eq[-1].this.rhs.astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[1].limits_subs(k, k - 1)
    
    Eq << Eq.induction.subs(Pascal.apply(n + 1, k))
    
    Eq << Eq[-1].this.rhs.astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[0].simplify()
    
    Eq << Eq[-1].this.rhs.args[1].simplify()
    
    Eq << Eq.induction.induct()
    
    Eq << algebre.sufficient.imply.condition.induction.apply(Eq[-1], n=n)

if __name__ == '__main__':
    prove(__file__)

