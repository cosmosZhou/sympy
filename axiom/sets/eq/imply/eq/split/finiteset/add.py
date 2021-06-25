from util import *

# given : A & B = A | B => A = B


@apply
def apply(given):
    x_y, _01 = given.of(Equal)
    x, y = x_y.of(FiniteSet)
    zero, one = _01.of(FiniteSet)

    assert zero.is_zero
    assert one.is_One
    return Equal(x + y, 1)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)

    Eq << apply(Equal({x, y}, {0, 1}))

    Eq << algebra.eq.imply.eq.reducedSum.apply(Eq[0])

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[-1].this.lhs.doit()

    Eq << sets.eq.imply.ne.apply(Eq[0])

    Eq << algebra.cond.cond.imply.cond.apply(Eq[-1], Eq[-2])

if __name__ == '__main__':
    run()

