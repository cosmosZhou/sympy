from sympy import *
from axiom.utility import prove, apply
from sympy.stats.crv_types import ChiSquaredDistribution, NormalDistribution    
from sympy.stats.rv import PDF, pspace
from axiom import calculus, algebre
import axiom


@apply(imply=True)
def apply(_Y, Y):
    X_squared_Sum = _Y.definition
    
    X_squared_Sum, *limits = axiom.is_LAMBDA(X_squared_Sum)
    
    k = axiom.limit_is_symbol(limits)
    
    assert X_squared_Sum.is_Sum
    i = X_squared_Sum.variable
    
    X = pspace(X_squared_Sum).value.base
    
    assert Y.is_random and X.is_random
    y = pspace(Y).symbol
    assert y >= 0
    assert not y.is_random
    assert isinstance(Y.distribution, ChiSquaredDistribution)
    
    assert k == Y.distribution.k
    
    assert X_squared_Sum.function == X[i] * X[i]
    assert X_squared_Sum.is_random
    
    return Equality(PDF(_Y[k])(y), PDF(Y)(y).doit())


@prove
def prove(Eq):
    i = Symbol.i(integer=True, nonnegative=True)
    X = Symbol.X(shape=(oo,), distribution=NormalDistribution(0, 1))
    assert X[i].is_extended_real
    assert X.is_random

    k = Symbol.k(integer=True, positive=True)
    Y = Symbol.Y(distribution=ChiSquaredDistribution(k))
    assert Y.is_extended_real
    assert Y.is_random    
    _Y = Symbol.Y(shape=(oo,), definition=LAMBDA[k](Sum[i:k](X[i] * X[i])))
    
    Eq << apply(_Y, Y)
    
    assert _Y.is_nonnegative
    assert _Y.is_finite
    
    Eq.induction = Eq[-1].subs(k, k + 1) 
    
    Eq << Eq[0].subs(k, k + 1) - Eq[0] + _Y[k]
    
    Eq.x_squared_y = Eq.induction.subs(Eq[-1])
    
    Eq << Eq.x_squared_y.lhs.this.doit(evaluate=False)
    
    Eq << Eq[-1].this.rhs.args[3].function.args[-1].doit(deep=False)
    
    (_y, *_), *_ = Eq[-1].rhs.args[-1].limits    
    y = Eq[1].lhs.symbol
    assert y.is_nonnegative
    Eq.hypothesis_k = Eq[1].subs(y, _y)
    
    Eq << Eq.hypothesis_k.this.lhs.args[0].args[0].definition
    
    Eq << Eq[-2].subs(Eq[-1])
    
#     Eq << Eq[-1].subs(Eq.x_squared_y)
    
    Eq << Eq[-1].this.lhs.expand()
    
    t = Symbol.t(domain=Interval(0, pi / 2))
    assert t.is_zero is None
    
    Eq << Eq[-1].this.rhs.args[-1].limits_subs(_y, y * sin(t) ** 2)
    
    Eq << Eq[-1].this.rhs.args[-1].function.powsimp()
    
#     Eq << Eq[-1].solve(Eq[-1].rhs.args[-1])
    
    Eq << calculus.trigonometry.wallis.beta.apply(1, k)
    
    x = Eq[-1].lhs.variable
    t = Eq[-2].rhs.args[-1].variable
    Eq << Eq[-1].this.lhs.limits_subs(x, t)

# expand the BETA function into gamma function
    Eq << Eq[-1].this.rhs.expand(func=True)
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.powsimp()    

    Eq.initial = Eq[1].subs(k, 1)
    
    Eq << Eq[0].subs(k, 1).doit(deep=False)
    
    Eq << Eq.initial.subs(Eq[-1])
    
    Eq << Eq[-1].lhs.this.doit(evaluate=False)
    
    Eq << Eq.induction.induct()

    Eq << algebre.equal.sufficient.imply.equal.induction.apply(Eq.initial, Eq[-1], n=k, start=1)


# https://www.asmeurer.com/blog/
if __name__ == '__main__':
    prove(__file__)
