from util import *


@apply(given=None)
def apply(given):
    n, (n_, (a, b)) = given.of(And[Equal[Expr % 2, 0], Element[Range]])

    assert n == n_
    b -= 1

    return Equivalent(given, Element(n, imageset(n, 2 * n, Range((a + 1) // 2, b // 2 + 1))))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b, n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 0) & Element(n, Range(a, b + 1)))

    Eq << algebra.equivalent.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.is_even.el.imply.el)

    Eq << Eq[-1].this.rhs.apply(sets.el.imply.et.is_even)


if __name__ == '__main__':
    run()

