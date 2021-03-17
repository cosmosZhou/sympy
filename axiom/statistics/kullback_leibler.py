from sympy import *
from axiom.utility import prove, apply


def KL(p, q, *limit):
    return Sum(p * log(p / q), *limit)


@apply
def apply(p, q):
    x = Symbol('x')
    y = Symbol('y')
    return GreaterThan(KL(p(x, y), q(x, y), (x,), (y,)), KL(p(x), q(x), (x,)))


@prove(surmountable=False)
def prove(Eq):
    p = Function.p(nargs=(1, 2), shape=(), real=True)
    q = Function.q(nargs=(1, 2), shape=(), real=True)
    Eq << apply(p, q)


if __name__ == '__main__':
    prove(__file__)
