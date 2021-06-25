from util import *


@apply(given=None)
def apply(given):
    n, (n_, (a, b)) = given.of(And[Equal[Expr % 2, 0], Contains[Range]])

    assert n == n_
    b -= 1

    return Equivalent(given, Contains(n, imageset(n, 2 * n, Range((a + 1) // 2, b // 2 + 1))))


@prove
def prove(Eq):
    from axiom import sets, algebra
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    n = Symbol.n(integer=True)

    Eq << apply(Equal(n % 2, 0) & Contains(n, Range(a, b + 1)))

    Eq << algebra.equivalent.given.cond.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.is_even.contains.imply.contains)

    Eq << Eq[-1].this.rhs.apply(sets.contains.imply.et.is_even)


if __name__ == '__main__':
    run()

