from util import *


@apply(given=None)
def apply(given):
    n, (n_, (a, b)) = given.of(And[Equal[Expr % 2, 1], Element[Range]])

    assert n == n_
    b -= 1

    return Equivalent(given, Element(n, imageset(n, 2 * n + 1, Range(a // 2, (b - 1) // 2 + 1))))


@prove
def prove(Eq):
    from axiom import sets, algebra
    a, b, n = Symbol(integer=True)

    Eq << apply(Equal(n % 2, 1) & Element(n, Range(a, b + 1)))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.is_odd.el.imply.el)

    Eq << Eq[-1].this.rhs.apply(sets.el.imply.et.is_odd)


if __name__ == '__main__':
    run()

# created on 2018-05-31
# updated on 2018-05-31
