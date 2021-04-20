from sympy import *
from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling
from axiom import discrete, algebra


@apply
def apply(n, k):
    return Equal(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)
    
    Eq << Eq[0].apply(algebra.cond.given.et.forall, cond=k < n)
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    
    k_ = Symbol.k(domain=Interval(1, n - 1, integer=True))
    Eq << discrete.combinatorics.stirling.second.recurrence.k_less_than_n.apply(n, k_)
    
    Eq << Eq[-1].apply(algebra.cond.imply.forall.restrict, (k_,))
    
    Eq << algebra.forall.given.et.apply(Eq[-2], cond=n.set)
    
    Eq << Eq[-1].this().function.simplify()


if __name__ == '__main__':
    prove()

from . import k_less_than_n
