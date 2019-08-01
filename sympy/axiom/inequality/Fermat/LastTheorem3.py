from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, cout, Eq, plausible
from sympy.core.relational import Unequality
from sympy.axiom.equality.discrete.combinatorics import binomial
from sympy.axiom.equality.trigonometry import cosine


def apply():
    x = Symbol('x', integer=True, positive=True)
    y = Symbol('y', integer=True, positive=True)
    z = Symbol('z', integer=True, positive=True)
    return Unequality(x ** 3 + y ** 3, z ** 3,
                    plausible=plausible(),
                    for_clause=(x, y, z))


from sympy.utility import check


@check
def prove():
    cout << apply()
    return
    x, y, z = Eq[-1].for_clause
    cout << Eq[-1].negated

    cout << binomial.theorem.apply(x, y, 3).doit().reversed - Eq[-1]

    cout << Eq[-1].subs(Eq[-1].lhs, 0)

    cout << (Eq[-1] + z ** 3).real_root(3)
    cout << Eq[1].subs(x ** 3, 0).real_root(3)
    cout << Eq[1].subs(y ** 3, 0).real_root(3)

    cosine_theorem = cosine.theorem.apply(Eq[-1], Eq[-2], Eq[-3])
    cout << cosine_theorem

    cout << (Eq[-1] * z).expand()

    cout << (Eq[-3] * x ** 2 + Eq[-4] * y ** 2).reversed

    cout << Eq[-1] + Eq[-2]

    cout << Eq[-1].subs(Eq[1]).simplifier()

    cout << -Eq[-1].reversed

    cout << Eq[-1] / (2 * x * y * z)

    cout << cosine_theorem * Eq[4]
    cout << Eq[-1].expand().subs(Eq[1])
    cout << Eq[-1].simplifier()

    cout << Eq[-1] / (x * y * (x + y))

    cout << Eq[-1] - 1

    cout << Eq[-1] / -2


if __name__ == '__main__':
    prove()
    print('plausibles_dict:')
    for index, eq in plausibles_dict(Eq).items():
        print("Eq[%d] : %s" % (index, eq))
