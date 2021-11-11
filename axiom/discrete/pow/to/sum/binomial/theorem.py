from util import *


@apply
def apply(x, y, n=None, var=None):
    if var is None:
        k = Symbol(integer=True)
    else:
        k = var
    if n is None:
        n = Symbol(integer=True, nonnegative=True)
        return Equal((x + y) ** n, Sum[k:0:n + 1](binomial(n, k) * x ** k * y ** (n - k)))
    elif n < 0:
        return
    else:
        return Equal((x + y) ** n, Sum[k:0:n + 1](binomial(n, k) * x ** k * y ** (n - k)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    x, y = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(x, y, n)

    Eq.induct = Eq[-1].subs(n, n + 1)

    Eq << Eq[-1] * (x + y)

    Eq << Eq[-1].this.lhs.powsimp()

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.rhs.expr.expand()

    Eq << Eq[-1].this.rhs.expr.powsimp()

    (k, *_), *_ = Eq[-1].rhs.limits
    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.limits.subs.offset, -1)

    Eq << discrete.binomial.to.add.Pascal.apply(n + 1, k)

    Eq << algebra.cond.given.et.subs.apply(Eq.induct, *Eq[-1].args)

    Eq << Eq[-1].this.rhs.apply(algebra.sum_mul.to.add)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n)


if __name__ == '__main__':
    run()

# created on 2020-10-10
# updated on 2020-10-10
