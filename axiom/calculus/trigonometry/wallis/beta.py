from util import *



@apply
def apply(m, n=1):
    m = sympify(m)
    n = sympify(n)

    x = Symbol(real=True)
    return Equal(Integral[x:0:S.Pi / 2](cos(x) ** (m - 1) * sin(x) ** (n - 1)),
                    beta(m / 2, n / 2) / 2)


@prove
def prove(Eq):
    from axiom import calculus
    m, n = Symbol(integer=True, positive=True)

    Eq << apply(m, n)

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << calculus.trigonometry.wallis.gamma.apply(m, n)


if __name__ == '__main__':
    run()

