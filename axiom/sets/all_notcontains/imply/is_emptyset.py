from util import *


@apply
def apply(given):
    (_e, A), (e, B) = given.of(All[NotContains])
    assert e == _e
    return Equal(A & B, e.emptySet)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)

    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(All[x: A](NotContains(x, B)))

    Eq << algebra.all.imply.ou.apply(Eq[0], simplify=False)

    Eq << ~Eq[-1]

    Eq << ~Eq[1]


if __name__ == '__main__':
    run()

