from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy.stats.crv_types import ChiSquared, ChiSquaredDistribution
from sympy.stats.rv import Density, RandomSymbol
from sympy import pi, Symbol
from sympy.stats import Normal
from axiom.trigonometry import Wallis
from sympy.concrete.expr_with_limits import Ref
from sympy.concrete.summations import Sum


@plausible
def apply(X, Y):
    i = Symbol('i', integer=True)

    assert isinstance(Y, RandomSymbol)
    y = Y.symbol
    assert isinstance(Y.pspace.distribution, ChiSquaredDistribution)
    k = Y.pspace.distribution.k
    return Equality(Density(Sum[i:k](X[i] * X[i]))(y), Density(Y)(y).doit())



from sympy.utility import check


@check
def prove(Eq):
    x = Symbol('x', shape=(oo,), real=True)
    i = Symbol('i', integer=True)
    X = Symbol('X', shape=(oo,), definition=Ref[i](Normal(x[i], 0, 1)))

    k = Symbol('k', integer=True, positive=True)
    Y = ChiSquared('y', k)

    Eq << apply(X, Y)
    y = Y.symbol

    Y = Symbol('Y', shape=(oo,), definition=Ref[k](Sum[i:k](X[i] * X[i])))

    assert y.is_nonnegative and Y.is_finite and Y.is_nonnegative
    
    Eq << Y.equality_defined()  # 1
    Eq << Eq[0].subs(Eq[-1].reversed)  # 2

    Eq << Eq[-1].subs(k, k + 1)  # 3

    Eq << Eq[1].subs(k, k + 1) - Eq[1] + Y[k]

    Eq << Eq[-2].subs(Eq[-1])
    Eq << Eq[-1].lhs.equality_defined()

    Eq << Eq[-1].this.rhs.args[3].function.args[-1].doit(deep=False)

    (_y, *_), *_ = Eq[-1].rhs.args[-1].limits
    Eq << Eq[0].subs(y, _y)

    Eq << Eq[-2].subs(Eq[-1])
    Eq << Eq[-1].subs(Eq[5])

    Eq << Eq[-1].this.lhs.expand()

    from sympy import sin
    t = Symbol('t', domain=Interval(0, pi / 2))
    assert t.is_zero is None
    
    Eq << Eq[-1].this.rhs.args[-1].limits_subs(_y, y * sin(t) ** 2)

    Eq << Eq[-1].this.rhs.args[-1].function.powsimp()

    Eq << Eq[-1].solve(Eq[-1].rhs.args[-1])

    Eq << Wallis.apply(1, k)
    (x, *_), *_ = Eq[-1].lhs.limits
    (t, *_), *_ = Eq[-2].lhs.limits
    Eq << Eq[-1].this.lhs.limits_subs(x, t)

# expand the BETA function into gamma function
    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Eq[2].subs(k, 1)
    Eq << Eq[1].subs(k, 1).doit(deep=False)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].lhs.equality_defined()


# https://www.asmeurer.com/blog/
if __name__ == '__main__':
    prove(__file__)
