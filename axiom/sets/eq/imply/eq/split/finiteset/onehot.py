from util import *


@apply
def apply(given):
    x_y, _01 = given.of(Equal)
    x, y = x_y.of(FiniteSet)
    zero, one = _01.of(FiniteSet)

    assert zero.is_zero
    assert one.is_One
    return Equal(Matrix([x, y]), Matrix([1 - KroneckerDelta(0, x), KroneckerDelta(0, x)]))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    Eq << apply(Equal({x, y}, {0, 1}))

    Eq << algebra.eq.given.et.split.matrix.apply(Eq[1])

    

    Eq << Contains(x, {x, y}, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq << sets.contains.imply.eq.kroneckerDelta.zero.apply(Eq[-1])

    Eq.x_equality = -Eq[-1] + 1

    Eq << Eq.x_equality.reversed

    Eq << sets.eq.imply.eq.split.finiteset.add.apply(Eq[0])

    Eq << Eq[-1] + Eq.x_equality

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << algebra.is_zero.imply.eq.apply(Eq[-1])


if __name__ == '__main__':
    run()

