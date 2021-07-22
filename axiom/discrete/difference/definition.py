from util import *


@apply
def apply(fx, x, n):
    k = fx.generate_var(x.free_symbols | n.free_symbols, integer=True)
    return Equal(Difference(fx, x, n),
                 Sum[k:0:n + 1]((-1) ** (n - k) * binomial(n, k) * fx.subs(x, x + k)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    f = Function.f(real=True)
    x = Symbol.x(real=True)
    fx = f(x)
    n = Symbol.n(integer=True, nonnegative=True, given=False)
    Eq << apply(fx, x, n)

    Eq.initial = Eq[0].subs(n, 0)

    Eq << Eq.initial.this.lhs.doit()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(discrete.difference.split, slice(0, 1))

    Eq << Eq[-1].this.lhs.expr.doit()

    Eq << Eq[-1].this.lhs.apply(discrete.difference.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond={0})

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.split, cond={n + 1})

    Eq.hypothesis = algebra.cond.imply.cond.subs.apply(Eq[0], x, x + 1)

    Eq << Eq.hypothesis - Eq[0]

    i = Eq[-1].find(Sum).variable
    Eq << Eq[-1].this.find(Sum).limits_subs(i, i - 1)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.to.add.split, cond={n + 1})

    Eq.split = Eq[-1].this.find(Sum).apply(algebra.sum.to.add.split, cond={0})

    Eq << Add(*Eq.split.rhs.args[2:]).this.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.rhs.expr.collect(Mul(*Eq[-1].rhs.expr.args[0].args[:-1]))

    Eq << discrete.binomial.to.add.Pascal.apply(n + 1, i)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq.split.subs(Eq[-1])

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.eq.suffice.imply.eq.induct.apply(Eq.initial, Eq[-1], n=n)


if __name__ == '__main__':
    run()

