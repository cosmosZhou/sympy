from util import *


@apply(given=None)
def apply(given):
    n, (n_, (a, b)) = given.of(And[Equal[Expr % 2, 1], Contains[Range]])

    assert n == n_
    b -= 1

    return Equivalent(given, Contains(n, imageset(n, 2 * n + 1, Range(a // 2, (b - 1) // 2 + 1))))


@prove
def prove(Eq):
    from axiom import sets, algebra
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    n = Symbol.n(integer=True)

    Eq << apply(Equal(n % 2, 1) & Contains(n, Range(a, b + 1)))

    Eq << algebra.equivalent.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.is_odd.contains.imply.contains)

    Eq << Eq[-1].this.rhs.apply(sets.contains.imply.et.is_odd)


if __name__ == '__main__':
    run()

