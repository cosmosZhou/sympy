from util import *


@apply
def apply(given):
    n, b = given.of(LessEqual)

    assert n.is_integer
    return Contains(n, Range(-oo, b + 1))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)

    Eq << apply(n <= b)

    Eq << Eq[-1].simplify()

    Eq << algebra.lt.given.le.apply(Eq[-1])


if __name__ == '__main__':
    run()

