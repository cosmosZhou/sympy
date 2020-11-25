from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from axiom.utility import plausible
from sympy.core.relational import Equality
from sympy.stats.crv_types import ChiSquaredDistribution, NormalDistribution
    
from sympy.stats.rv import PDF, pspace
from sympy import pi
from axiom.calculus.trigonometry import wallis
from sympy.concrete.expr_with_limits import LAMBDA
from sympy.concrete.summations import Sum
from sympy import Symbol


@plausible
def apply(X, Y):
    i = Symbol.i(integer=True)

    assert Y.is_random and X.is_random
    y = pspace(Y).symbol
    assert y >= 0
    assert not y.is_random
    assert isinstance(Y.distribution, ChiSquaredDistribution)
    k = Y.distribution.k
    assert Sum[i:k](X[i] * X[i]).is_random
    
    return Equality(PDF(Sum[i:k](X[i] * X[i]))(y), PDF(Y)(y).doit())


from axiom.utility import check


@check
def prove(Eq):
    i = Symbol.i(integer=True, nonnegative=True)
    X = Symbol.X(shape=(oo,), distribution=NormalDistribution(0, 1))
    assert X[i].is_extended_real
    assert X.is_random

    k = Symbol.k(integer=True, positive=True)
    Y = Symbol.Y(distribution=ChiSquaredDistribution(k))
    assert Y.is_extended_real
    assert Y.is_random    

    Eq << apply(X, Y)

    Y = Symbol.Y(shape=(oo,), definition=LAMBDA[k](Sum[i:k](X[i] * X[i])))    
    assert Y.is_nonnegative
    assert Y.is_finite
    
    Eq << Y.equality_defined()  # 1
    Eq << Eq[0].subs(Eq[-1].reversed)  # 2

    Eq << Eq[-1].subs(k, k + 1)  # 3

    Eq << Eq[1].subs(k, k + 1) - Eq[1] + Y[k]  # 4

    Eq.x_squared_y = Eq[-2].subs(Eq[-1])  # 5
    Eq << Eq.x_squared_y.lhs.this.doit(evaluate=False)

    Eq << Eq[-1].this.rhs.args[3].function.args[-1].doit(deep=False)

    (_y, *_), *_ = Eq[-1].rhs.args[-1].limits    
    y = Eq[0].lhs.symbol
    assert y.is_nonnegative
    Eq << Eq[0].subs(y, _y)

    Eq << Eq[-2].subs(Eq[-1])
    Eq << Eq[-1].subs(Eq.x_squared_y)

    Eq << Eq[-1].this.lhs.expand()

    from sympy import sin
    t = Symbol.t(domain=Interval(0, pi / 2))
    assert t.is_zero is None
    
    Eq << Eq[-1].this.rhs.args[-1].limits_subs(_y, y * sin(t) ** 2)

    Eq << Eq[-1].this.rhs.args[-1].function.powsimp()

    Eq << Eq[-1].solve(Eq[-1].rhs.args[-1])

    Eq << wallis.apply(1, k)
    (x, *_), *_ = Eq[-1].lhs.limits
    (t, *_), *_ = Eq[-2].lhs.limits
    Eq << Eq[-1].this.lhs.limits_subs(x, t)

# expand the BETA function into gamma function
    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Eq[2].subs(k, 1)
    Eq << Eq[1].subs(k, 1).doit(deep=False)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].lhs.this.doit(evaluate=False)


# https://www.asmeurer.com/blog/
if __name__ == '__main__':
    prove(__file__)
