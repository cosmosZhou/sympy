from util import *


def is_infinite_series(fx):
    f, (n, a, b) = fx.of(Sum)
    assert n.is_integer
    assert b.is_infinite
    if not a.is_zero:
        f = f._subs(n, n + a)
    return f


@apply
def apply(given, x):
    
    lhs, rhs = given.of(Equal)
    an = is_infinite_series(lhs)
    bn = is_infinite_series(rhs)
    n = lhs.variable
    an /= x ** n
    bn /= x ** n
    return Equal(an, bn)


@prove
def prove(Eq):
    from axiom import algebra, calculus

    A = Symbol.A(shape=(oo,), real=True)
    B = Symbol.B(shape=(oo,), real=True)
    x = Symbol.x(real=True)
    n = Symbol.n(integer=True)
    Eq << apply(Equal(Sum[n:0:oo](A[n] * x ** n), Sum[n:0:oo](B[n] * x ** n)), x=x)

    Eq << Eq[0].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[3].subs(x, 0)

    Eq << Eq[-1].this.lhs().function.simplify()

    Eq.initial = Eq[-1].this.rhs().function.simplify()

    m = Symbol.m(integer=True, given=False, nonnegative=True)
    Eq.hypothesis = Eq[1].subs(n, m)

    Eq.induct = Eq.hypothesis.subs(m, m + 1)

    k = Symbol.k(domain=Range(0, m + 1))
    Eq.hypothesis_k = Eq.hypothesis.subs(m, k)

    Eq << Eq.hypothesis_k * x ** k

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (k,))

    _k = Symbol.k(integer=True)
    Eq << Eq[-1].this.lhs.limits_subs(k, _k)

    Eq << Eq[-1].this.rhs.limits_subs(k, _k)

    Eq << Eq[3].this.lhs.limits_subs(n, _k)

    Eq << Eq[3].this.rhs.limits_subs(n, _k)

    Eq << Eq[3] - Eq[-1]

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.sum.limits.complement)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum.limits.complement)

    r = Symbol.r(real=True, positive=True)
    Eq << Eq[-1].subs(x, r)

    Eq << Eq[-1].this.lhs.limits_subs(_k, _k + m + 1)

    Eq << Eq[-1].this.rhs.limits_subs(_k, _k + m + 1)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.mul)

    Eq << calculus.eq.imply.eq.limit.apply(Eq[-1], (r, 0))

    Eq << Eq[-1].this.lhs.apply(calculus.limit.to.sum)

    Eq << Eq[-1].this.rhs.apply(calculus.limit.to.sum)

    Eq << Eq[-1].this.lhs.split({0})

    Eq << Eq[-1].this.rhs.split({0})

    Eq << Eq[-1].this.lhs.args[1]().function.doit()

    Eq << Eq[-1].this.rhs.args[1]().function.doit()

    Eq << Suffice(Eq.hypothesis_k, Eq.induct, plausible=True)

    Eq << algebra.cond.suffice.imply.cond.induct.second.apply(Eq.initial, Eq[-1], n=m + 1, k=k, hypothesis=True)

    Eq << Eq.induct.subs(m, m - 1)

    Eq << Eq.hypothesis.subs(m, n)


if __name__ == '__main__':
    run()

