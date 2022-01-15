from util import *



@apply
def apply(m, n=1):
    m = sympify(m)
    n = sympify(n)

    x = Symbol(real=True)
    return Equal(Integral[x:0:S.Pi / 2](cos(x) ** (m - 1) * sin(x) ** (n - 1)),
                    gamma(m / 2) * gamma(n / 2) / (2 * gamma((m + n) / 2)))


@prove
def prove(Eq):
    from axiom import calculus, algebra
    #m is the inductive variable
    m = Symbol(integer=True, positive=True, given=False)
    #n is not a inductive variable
    n = Symbol(integer=True, positive=True)

    Eq << apply(m, n)

    (x, *_), *_ = Eq[0].lhs.limits

    Eq.one = Eq[0].subs(m, 1)

    Eq << calculus.trigonometry.sine.wallis.apply(n)

    Eq.induct = Eq[0].subs(m, m + 2)

    Eq << Eq.induct.this.lhs.expr.expand()

    Eq << Eq[-1].this.lhs.apply(calculus.integral.to.add.by_parts, u=cos(x) ** m)

    Eq << Eq[-1] / (m / n)

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << algebra.cond.imply.cond.subs.apply(Eq[0], n, n + 2)

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Eq[-1].this.lhs.expand()

    Eq.two = Eq[0].subs(m, 2)

    t = Symbol(domain=Interval(0, 1))
    Eq << Eq.two.this.lhs.limits_subs(sin(x), t)

    Eq << calculus.integral.to.mul.st.pow.apply(n - 1, b=1, x=t)

    Eq << Eq[-2] - Eq[-1]

    Eq << Eq[-1] + 1 / n

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.eq.eq.infer.imply.eq.induct.apply(Eq.one, Eq.two, Eq[-1], n=m, start=1)


if __name__ == '__main__':
    run()

# created on 2020-07-01
