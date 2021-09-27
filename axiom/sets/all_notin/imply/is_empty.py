from util import *


@apply
def apply(given):
    (_e, A), (e, B) = given.of(All[NotElement])
    assert e == _e
    return Equal(A & B, e.emptySet)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True)

    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(All[x: A](NotElement(x, B)))

    Eq << algebra.all.imply.ou.apply(Eq[0], simplify=False)

    Eq << ~Eq[-1]

    Eq << ~Eq[1]


if __name__ == '__main__':
    run()

