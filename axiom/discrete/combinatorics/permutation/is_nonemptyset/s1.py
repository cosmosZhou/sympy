from sympy import *
from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling
from axiom import sets, algebre


@apply
def apply(n, k=None):
    if k is None:
        k = Symbol.k(domain=Interval(1, n, integer=True))
    assert k <= n and k > 0
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)            
    s = Stirling.conditionset(n, k, x)
    return Unequality(s, s.etype.emptySet)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    k = Symbol.k(domain=Interval(1, n, integer=True), given=True)
    Eq << apply(n, k=k)    
    
    Eq << sets.is_nonemptyset.given.exists.where.conditionset.apply(Eq[0])
    
    i = Symbol.i(integer=True)
    x, (_, k), *_ = Eq[-1].variable.args
    
    a = Symbol.a(LAMBDA[i:k](Piecewise((Interval(k - 1, n - 1, integer=True),
                                                   Equality(i, k - 1)),
                                                   (i.set, True))))
    
    Eq << algebre.exists.given.exists.subs.apply(Eq[-1], x[:k], a)
    
    Eq.is_positive, Eq.sum, Eq.union = Eq[-1].split()
    
    Eq << Eq.is_positive.this.function.lhs.arg.definition
    
    Eq << Eq.sum.this.lhs.function.arg.definition
    
    Eq << Eq.union.this.lhs.function.definition
    

if __name__ == '__main__':
    prove(__file__)

