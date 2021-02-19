from sympy import *
from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling
from axiom import discrete, algebre
from sympy.sets.conditionset import conditionset


@apply
def apply(n, k):
    return Equality(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)
    
    Eq << Eq[0].bisect(k < n).split()
    
    k_ = Symbol.k(domain=Interval(1, n - 1, integer=True))
    Eq << discrete.combinatorics.stirling.second.recurrence.k_less_than_n.apply(n, k_)
    
    Eq << Eq[-1].apply(algebre.condition.imply.forall.minify, (k_,))
    
    Eq << Eq[-2].bisect(n.set).split()
    
    Eq << Eq[-1].this().function.simplify()


if __name__ == '__main__':
    prove(__file__)

