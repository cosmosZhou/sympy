from util import *


@apply
def apply(r, n):
    if not n >= 2:
        return None
    k = Symbol.k(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(domain=Range(0, n))

    A = Lamda[j, i:n - 1]((j + 1) ** (i + 1))
    R = Lamda[j](1 - r ** (j + 1))
# note : [A, B].T = (A.T, B.T)
# [R, A] = (R.T, A.T).T

    return Equal(Det([R, A]), (1 - r) ** n * Product[k:1:n](factorial(k)))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    r = Symbol.r(real=True)
    n = Symbol.n(domain=Range(2, oo))

    Eq << apply(r, n)

    (j, *_), (i, *iab) = Eq[0].lhs.arg.args[1].limits

    assert (2 * i).is_even

    E = Lamda[j, i:n]((-1) ** (j - i) * binomial(j + 1, i + 1))

    Eq << (Eq[0].lhs.arg @ E).this.expand()

    (k, *_), *_ = Eq[-1].rhs.args[1].function.limits

    _i = i.copy(domain=Range(*iab))
    Eq << discrete.combinatorics.stirling.second.definition.apply(_i + 1, j + 1)

    Eq << Eq[-1] * factorial(j + 1)
    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].forall((_i,))

    Eq << Eq[1].rhs.args[1].function.this.limits_subs(k, k - 1)

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq[-2], Eq[-1])

    Eq.equation = algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq[1])

    i_ = Eq.equation.rhs.args[0].function.variable
    Eq << Eq.equation.rhs.args[0].function.this.limits_subs(i_, i_ - 1)

    i = Eq[-1].rhs.variable

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.args[1].simplify()

    Eq << discrete.combinatorics.binomial.theorem.apply(r, -1, j + 1, i)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.args[1].simplify()

    Eq << Eq[-4] + (Eq[-1] - Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].this.rhs.args[-1].args[-1].function.powsimp()

    Eq << discrete.combinatorics.binomial.theorem.apply(1, -1, j + 1, i)

    Eq << (-Eq[-1]).this.rhs.astype(Sum)

    Eq << Eq[-3] + Eq[-1]

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq.equation.subs(Eq[-1])

    Eq << Shift(n, 0, n - 1) @ Eq[-1]

    Eq << Eq[-1].apply(algebra.eq.imply.eq.det)

    Eq << Eq[-1] * (-1) ** (n - 1)

    Eq << Eq[-1].this.rhs.powsimp()

    v = Eq[-1].rhs.args[1].variable
    Eq << Eq[-1].this.rhs.args[1].limits_subs(v, v - 1)


if __name__ == '__main__':
    run()
