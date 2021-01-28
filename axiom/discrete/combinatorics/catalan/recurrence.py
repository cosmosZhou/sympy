from sympy import *
from axiom.utility import prove, apply
from axiom import discrete, algebre, calculus, sets
import axiom


@apply(imply=True)
def apply(*given, n=None):
    C0_definition, Cn1_definition = given
    
    C0, one = axiom.is_Equal(C0_definition)
    assert one.is_One
    
    Cn1, summation = axiom.is_Equal(Cn1_definition)
    Cn = Cn1._subs(n, n - 1)
    assert Cn._subs(n, 0) == C0

    return Equality(Cn, binomial(n * 2, n) / (n + 1))


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True)
    
    C = Symbol.C(shape=(oo,), integer=True)
    
    Eq << apply(Equality(C[0], 1),
                Equality(C[n + 1], Sum[k:n + 1](C[k] * C[n - k])), n=n)
    
    m = Symbol.m(integer=True)

    x = Symbol.x(domain=Interval(0, S.One / 4, left_open=True))

    def g(x):
        return Sum[n:oo](C[n] * x ** n)
    
    g = Function.g(eval=g)
    
    Eq.g_definition = g(x).this.definition
    
    Eq << Eq[1] * x ** n
    
    Eq << algebre.equal.imply.equal.sum.apply(Eq[-1], (n, 0, oo))

    Eq << calculus.series.infinite.product.apply(C, C, n=n, k=k, x=x)
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-2], Eq[-1])

    Eq << Eq.g_definition ** 2
    
    Eq.g_squared = algebre.equal.equal.imply.equal.transit.apply(Eq[-2], Eq[-1])
    
    Eq << Eq.g_definition.this.rhs.bisect(Slice[1:])
    
    Eq << Eq[-1] + Eq[0]
    
    Eq << Eq[-1] - 1
    
    Eq << Eq[-1].this.rhs.limits_subs(n, n + 1)
    
    Eq << Eq.g_squared * x
    
    Eq << Eq[-1].this.lhs.astype(Sum)
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-1], Eq[-3])
    
    Eq.negative_sqrt, Eq.positive_sqrt = Eq[-1].apply(algebre.equal.imply.ou.quadratic, x=g(x), simplify=False).split()
    
    Eq << algebre.equal.imply.equal.limit.apply(Eq.g_definition, x, 0)
    
    Eq << Eq[-1].this.rhs.astype(Sum)
    
    Eq << Eq[-1].this.rhs.bisect(Slice[1:])
    
    Eq << Eq[-1].this.rhs.args[0].doit()
    
    Eq << Eq[-1].this.rhs.args[1]().function.doit()
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-1], Eq[0])
    
    Eq << algebre.equal.imply.equal.limit.apply(Eq.positive_sqrt, x, 0) 
    
    Eq << Eq[-1].this.rhs.doit()
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-1], Eq[-3])

    Eq << calculus.series.infinite.binomial.apply(S.One / 2, x=-4 * x, n=n)

    Eq << discrete.combinatorics.binomial.half.apply(n)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.args[1].function.powsimp()
    
    Eq << Eq[-1].this.rhs.args[1].bisect(Slice[1:])
    
    Eq << 1 - Eq[-1]
    
    Eq << Eq[-1].this.rhs.limits_subs(n, n + 1)
    
    Eq << Eq[-1] / (x * 2)
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq.g_series = Eq[-1] + Eq.negative_sqrt.this.rhs.expand()
    
    Eq << discrete.combinatorics.binomial.fraction.apply(2 * n + 2, n + 1)
    
    Eq << discrete.combinatorics.binomial.expand.apply(2 * n + 1, n + 1)
    
    Eq << Eq[-2].subs(Eq[-1]) * (2 * n + 2)
    
    Eq << Eq.g_series.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.astype(Sum)
    
    Eq << Eq[-1].this.rhs.function.ratsimp()        
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-1], Eq.g_definition)
    
    Eq << algebre.equal.imply.equal.series.infinite.coefficient.apply(Eq[-1].reversed, x=x)

    
if __name__ == '__main__':
    prove(__file__)

