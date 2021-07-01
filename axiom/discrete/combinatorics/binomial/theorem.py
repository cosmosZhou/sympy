from util import *


@apply
def apply(x, y, n=None, var=None):
    if var is None:
        k = Symbol.k(integer=True)
    else:
        k = var
    if n is None:
        n = Symbol.n(integer=True, nonnegative=True)
        return Equal((x + y) ** n, Sum[k:0:n + 1](binomial(n, k) * x ** k * y ** (n - k)))
    elif n < 0:
        return
    else:
        return Equal((x + y) ** n, Sum[k:0:n + 1](binomial(n, k) * x ** k * y ** (n - k)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    n = Symbol.n(integer=True, nonnegative=True, given=False)
    Eq << apply(x, y, n)

    Eq.induct = Eq[-1].subs(n, n + 1)

    Eq << Eq[-1] * (x + y)

    Eq << Eq[-1].this.lhs.powsimp()

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq[-1].this.rhs.function.powsimp()

    (k, *_), *_ = Eq[-1].rhs.limits
    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.args[1].limits_subs(k, k - 1)

    Eq << Eq.induct.subs(discrete.combinatorics.binomial.Pascal.apply(n + 1, k))

    Eq << Eq[-1].this.rhs.apply(algebra.sum_mul.to.add)

    Eq << Eq[-1].this.rhs.args[0].simplify()

    Eq << Eq[-1].this.rhs.args[1].simplify()

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=n)


if __name__ == '__main__':
    run()

