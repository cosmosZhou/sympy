from util import *


@apply
def apply(x, n):
    if not x.is_Symbol:
        return
    return Equal(Difference(x ** n, x, n), factorial(n))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol.x(real=True)

    k = Symbol.k(integer=True, nonnegative=True)
    t = x ** k
    assert t.is_complex
    assert t.is_extended_real

    n = Symbol.n(integer=True, nonnegative=True, given=False)
    Eq << apply(x, n)

    Eq.initial = Eq[0].subs(n, 0)

    Eq << Eq.initial.this.lhs.doit()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(discrete.difference.split, Slice[:1])

    Eq << Eq[-1].this.lhs.expr.doit()

    Eq << discrete.combinatorics.binomial.theorem.apply(x, 1, n + 1) - x ** (n + 1)

    Eq << Eq[-1].this.rhs.args[1].split(Slice[-1:])

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.difference.to.sum)

    Eq << Eq[-1].this.lhs.split(n.set)

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)

    _k = Symbol.k(domain=Range(0, n))

    Eq << Eq[0].subs(n, _k)

    Eq << discrete.eq.imply.eq.difference.apply(Eq[-1], (x, n - _k))

    Eq << Eq[-1].this.lhs.as_one_term()

    Eq << Eq[-1] * binomial(n + 1, _k)

    Eq << Eq[-1].apply(algebra.eq.imply.eq.sum, (_k,))

    Eq << Eq[-1].this.lhs.limits_subs(_k, k)

    Eq << Eq[0] * (n + 1)

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq.induct.induct()

    Eq << Eq[-1].this.lhs.forall((_k,))

    Eq << algebra.cond.suffice.imply.cond.induct.second.split.all.apply(Eq.initial, Eq[-1], n=n)

    Eq << Eq[0].subs(n, _k)


if __name__ == '__main__':
    run()

