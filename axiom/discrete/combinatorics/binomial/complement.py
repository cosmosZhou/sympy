from axiom.utility import prove, apply
from sympy import *


@apply
def apply(n, k):
    return Equal(binomial(n, k), binomial(n, n - k))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    k = Symbol.k(integer=True)

    Eq << apply(n, k)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    prove()
