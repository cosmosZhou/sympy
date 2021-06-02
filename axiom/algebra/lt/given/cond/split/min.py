from util import *

import axiom


@apply
def apply(given):
    x, max_ab = given.of(Less)
    ab = max_ab.of(Min)
    return tuple(x < a for a in ab)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)

    Eq << apply(x < Min(a, b))

    Eq << algebra.lt.lt.imply.lt.min.apply(Eq[1], Eq[2])

if __name__ == '__main__':
    run()
