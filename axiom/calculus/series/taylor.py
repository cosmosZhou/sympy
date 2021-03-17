from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre


@apply
def apply(n):
    k = Symbol.k(integer=True)
    return Equality(Limit[n:oo](Sum[k:1:n](1 / k) / log(n + 1)), 1)


@prove(surmountable=False)
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)


if __name__ == '__main__':
    prove(__file__)

