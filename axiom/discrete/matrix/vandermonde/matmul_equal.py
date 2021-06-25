from util import *


@apply
def apply(x, m, n, d, delta):
    i = Symbol.i(domain=Range(0, m - d))
    j = Symbol.j(domain=Range(0, n))
    h = Symbol.h(integer=True)

    return Equal(Lamda[j:m, i](binomial(d, j - i) * (-1) ** (d + i - j)) @ Lamda[j, i:m]((i + delta) ** j * x ** i),
                 Lamda[j, i]((i + delta) ** j * x ** i) @ Lamda[j, i:n](binomial(j, i) * Sum[h:d + 1](binomial(d, h) * (-1) ** (d - h) * x ** h * h ** (j - i))))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol.n(domain=Range(1, oo))
    m = Symbol.m(domain=Range(1, oo))
    d = Symbol.d(domain=Range(0, oo))

    i = Symbol.i(domain=Range(0, m - d))
    j = Symbol.j(domain=Range(0, n))
    h = Symbol.h(integer=True)

    delta = Symbol.delta(real=True)

    x = Symbol.x(real=True)

    Eq << apply(x, m, n, d, delta)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1][i, j]

    Eq << Eq[-1].this.rhs.args[1].limits_swap()

    Eq << Eq[-1].this.rhs.args[1].limits_subs(h, h - i)

    Eq.distribute = Eq[-1].this.rhs.apply(algebra.mul.to.sum)

    Eq << Eq.distribute.this.lhs.limits_subs(Eq.distribute.lhs.variable, h)

    Eq << discrete.combinatorics.binomial.theorem.apply(delta + i, h - i, j).reversed

    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, Eq.distribute.rhs.function.args[-1].variable)

    Eq << Eq.distribute.this.rhs.subs(Eq[-1])

    Eq << Eq[3].apply(algebra.eq.imply.eq.lamda, (j,), (i,), simplify=False)


if __name__ == '__main__':
    run()
