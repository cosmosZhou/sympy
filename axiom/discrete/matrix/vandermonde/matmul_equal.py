from sympy import *
from axiom.utility import prove, apply
import axiom

from axiom import algebre


@apply
def apply(x, m, n, d, delta):
    i = Symbol.i(domain=Interval(0, m - d, right_open=True, integer=True))
    j = Symbol.j(domain=Interval(0, n, right_open=True, integer=True))
    h = Symbol.h(integer=True)

    return Equality(LAMBDA[j:m, i](binomial(d, j - i) * (-1) ** (d + i - j)) @ LAMBDA[j, i:m]((i + delta) ** j * x ** i),
                    LAMBDA[j, i]((i + delta) ** j * x ** i) @ LAMBDA[j, i:n](binomial(j, i) * Sum[h:d + 1](binomial(d, h) * (-1) ** (d - h) * x ** h * h ** (j - i))))


@prove
def prove(Eq):
    n = Symbol.n(domain=Interval(1, oo, right_open=True, integer=True))
    m = Symbol.m(domain=Interval(1, oo, right_open=True, integer=True))
    d = Symbol.d(domain=Interval(0, oo, right_open=True, integer=True))

    i = Symbol.i(domain=Interval(0, m - d, right_open=True, integer=True))
    j = Symbol.j(domain=Interval(0, n, right_open=True, integer=True))
    h = Symbol.h(integer=True)

    delta = Symbol.delta(real=True)
    
    x = Symbol.x(real=True)

    Eq << apply(x, m, n, d, delta)

    Eq << Eq[-1].expand()

    Eq << Eq[-1][i, j]

    Eq << Eq[-1].this.rhs.args[1].limits_swap()

    Eq << Eq[-1].this.rhs.args[1].limits_subs(h, h - i)
    
    Eq.distribute = Eq[-1].this.rhs.astype(Sum)
   
    Eq << Eq.distribute.this.lhs.limits_subs(Eq.distribute.lhs.variable, h)

    Eq << axiom.discrete.combinatorics.binomial.theorem.apply(delta + i, h - i, j).reversed

    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, Eq.distribute.rhs.function.args[-1].variable)

    Eq << Eq.distribute.this.rhs.subs(Eq[-1])

    Eq << Eq[2].apply(algebre.equal.imply.equal.lamda, (j,), (i,), simplify=False)


if __name__ == '__main__':
    prove(__file__)
