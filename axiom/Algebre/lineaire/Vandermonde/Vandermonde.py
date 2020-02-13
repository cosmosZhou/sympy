from sympy.functions.combinatorial.factorials import binomial
from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, plausible
from sympy.core.relational import Equality
import axiom


def apply(x, m, n, d, delta):
    i = Symbol('i', domain=Interval(0, m - d, right_open=True, integer=True))
    j = Symbol('j', domain=Interval(0, n, right_open=True, integer=True))
    h = Symbol('h', integer=True)

    return Equality(Ref[i, j:m](binomial(d, j - i) * (-1) ** (d + i - j)) @ Ref[i:m, j]((i + delta) ** j * x ** i),
                    Ref[i, j]((i + delta) ** j * x ** i) @ Ref[i:n, j](binomial(j, i) * Sum[h:0:d](binomial(d, h) * (-1) ** (d - h) * x ** h * h ** (j - i))),
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', domain=Interval(1, oo, right_open=True, integer=True))
    m = Symbol('m', domain=Interval(1, oo, right_open=True, integer=True))
    d = Symbol('d', domain=Interval(0, oo, right_open=True, integer=True))

    i = Symbol('i', domain=Interval(0, m - d, right_open=True, integer=True))
    j = Symbol('j', domain=Interval(0, n, right_open=True, integer=True))
    h = Symbol('h', integer=True)

    delta = Symbol('delta', real=True)
    x = Symbol('x', real=True)

    Eq << apply(x, m, n, d, delta)

    Eq << Eq[-1].expand()

    Eq << Eq[-1][i, j]

    Eq << Eq[-1].this.rhs.swap()

    Eq << Eq[-1].this.rhs.limits_subs(h, h - i)
   
    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, h)

#     Eq << Eq[-1].this.rhs.function.args[-1].simplifier()

    Eq << axiom.discrete.combinatorics.binomial.theorem.apply(delta + i, h - i, j).reversed

    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, Eq[-2].rhs.function.args[-1].variable)

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[2].reference((i,), (j,))


if __name__ == '__main__':
    prove(__file__)
