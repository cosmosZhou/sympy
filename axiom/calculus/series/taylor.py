from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre


@apply(imply=True)
def apply(n):
    k = Symbol.k(integer=True)
    return Equality(Limit(Sum[k:1:n](1 / k) / log(n + 1), n, oo), 1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)

if __name__ == '__main__':
    prove(__file__)

