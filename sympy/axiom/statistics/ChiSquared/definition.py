from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, cout, Eq, plausible
from sympy.core.relational import Equality
from sympy.stats.crv_types import ChiSquared
from sympy.stats.rv import Density
from sympy import pi, Symbol
from sympy.stats import Normal
from sympy.tensor.indexed import IndexedBase
from sympy.axiom.trigonometry import Wallis


def apply():
    i = Symbol('i', integer=True)
    k = Symbol('k', integer=True, positive=True)
    x = IndexedBase('x', (oo,))

    X = IndexedBase('X', (oo,), definition=Ref[i](Normal(x[i], 0, 1)))

    Y = ChiSquared('y', k)
    y = Y.symbol

    return Equality(Density(Sum[i:k](X[i] * X[i]))(y), Density(Y)(y).doit(),
                    for_clause=(y, k),
                    where=X,
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    cout << apply()  # 0
    y, k = Eq[0].for_clause
    X = Eq[0].where
    i = Symbol('i', integer=True)

    Y = IndexedBase('Y', (oo,), definition=Ref[k](Sum[i:k](X[i] * X[i])))

    cout << Equality.by_definition_of(Y)  # 1
    cout << Eq[0].subs(Eq[-1].reversed)  # 2

    cout << Eq[-1].subs(k, k + 1)  # 3

    cout << Eq[1].subs(k, k + 1) - Eq[1] + Y[k]

    cout << Eq[-2].subs(Eq[-1])

    cout << Equality.by_definition_of(Eq[-1].lhs)

    cout << Eq[-1].right.function.args[0].doit()

    (_y, *_), *_ = Eq[-1].rhs.args[-1].limits
    cout << Eq[0].subs(y, _y)

    cout << Eq[-2].subs(Eq[-1])

    cout << Eq[-1].subs(Eq[5])

    cout << Eq[-1].left.expand()

    from sympy import sin
    t = Symbol('t', domain=Interval(0, pi / 2))
    cout << Eq[-1].right.args[-1].subs_limits(_y, y * sin(t) ** 2)

    cout << Eq[-1].right.args[-1].function.powsimp()

    cout << Eq[-1].solve(Eq[-1].rhs.args[-1])

    cout << Wallis.apply(1, k)

    (x, *_), *_ = Eq[-1].lhs.limits
    (t, *_), *_ = Eq[-2].lhs.limits
    cout << Eq[-1].left.subs_limits(x, t)

# expand the BETA function into gamma function
    cout << Eq[-1].right.expand(func=True)

    cout << Eq[2].subs(k, 1)
    cout << Eq[1].subs(k, 1).doit()

    cout << Eq[-2].subs(Eq[-1])

    cout << Equality.by_definition_of(Eq[-1].lhs)


# https://www.asmeurer.com/blog/
if __name__ == '__main__':
    prove()
