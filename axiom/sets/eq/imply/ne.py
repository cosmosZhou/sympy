from util import *


# given : A & B = A | B => A = B


@apply
def apply(given):
    x_y, _01 = given.of(Equal)
    x, y = x_y.of(FiniteSet)
    zero, one = _01.of(FiniteSet)

    assert zero.is_zero
    assert one.is_One
    return Unequal(x, y)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)

    Eq << apply(Equal({x, y}, {0, 1}))

    Eq << ~Eq[-1]

    Eq << Eq[0].subs(Eq[-1])

if __name__ == '__main__':
    run()

