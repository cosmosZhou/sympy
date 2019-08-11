from sympy.functions.combinatorial.factorials import binomial
from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, cout, Eq, plausible
from sympy.core.relational import Equality
from sympy import axiom


def apply(x, m, n, d, delta):
    i = Symbol('i', domain=Interval(0, m - d, right_open=True, integer=True))
    j = Symbol('j', domain=Interval(0, n, right_open=True, integer=True))
    h = Symbol('h', integer=True)

    return Equality(Ref[i, j:m](binomial(d, j - i) * (-1) ** (d + i - j)) @ Ref[i:m, j]((i + delta) ** j * x ** i),
                    Ref[i, j]((i + delta) ** j * x ** i) @ Ref[i:n, j](binomial(j, i) * Sum[h:0:d](binomial(d, h) * (-1) ** (d - h) * x ** h * h ** (j - i))),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    n = Symbol('n', domain=Interval(1, oo, right_open=True, integer=True))
    m = Symbol('m', domain=Interval(1, oo, right_open=True, integer=True))
    d = Symbol('d', domain=Interval(0, oo, right_open=True, integer=True))

    i = Symbol('i', domain=Interval(0, m - d, right_open=True, integer=True))
    j = Symbol('j', domain=Interval(0, n, right_open=True, integer=True))
    h = Symbol('h', integer=True)

    delta = Symbol('delta', real=True)
    x = Symbol('x', real=True)

    cout << apply(x, m, n, d, delta)

    cout << Eq[-1].expand().subscript(i, j)

    cout << Eq[-1].right.swap()

    cout << Eq[-1].right.subs_limits(h, h - i)

    (k, *_), *_ = Eq[3].left.limits
    cout << Eq[-1].left.subs_limits(k, h)

    cout << Eq[-1].right.function.args[-1].simplifier()

    cout << axiom.discrete.combinatorics.binomial.theorem.apply(delta + i, h - i, j).reversed

    cout << Eq[-1].left.subs_limits(Eq[-1].lhs.limits[0][0], k)

    cout << Eq[-3].right.subs(Eq[-1])

#     cout << Eq[-1].left.simplifier()


if __name__ == '__main__':
    prove()
