from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, Eq, plausible
from sympy.core.relational import Unequality
from sympy.axiom.discrete.combinatorics import binomial
from sympy.axiom.trigonometry import cosine


def apply():
    x = Symbol('x', integer=True, positive=True)
    y = Symbol('y', integer=True, positive=True)
    z = Symbol('z', integer=True, positive=True)
    return Unequality(x ** 3 + y ** 3, z ** 3,
                    plausible=plausible(),
                    forall=(x, y, z))


from sympy.utility import check


@check
def prove(Eq):
    Eq << apply()
    return
    x, y, z = Eq[-1].forall
    Eq << ~Eq[-1]

    Eq << binomial.theorem.apply(x, y, 3).doit().reversed - Eq[-1]

    Eq << Eq[-1].subs(Eq[-1].lhs, 0)

    Eq << (Eq[-1] + z ** 3).real_root(3)
    Eq << Eq[1].subs(x ** 3, 0).real_root(3)
    Eq << Eq[1].subs(y ** 3, 0).real_root(3)

    cosine_theorem = cosine.theorem.apply(Eq[-1], Eq[-2], Eq[-3])
    Eq << cosine_theorem

    Eq << (Eq[-1] * z).expand()

    Eq << (Eq[-3] * x ** 2 + Eq[-4] * y ** 2).reversed

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1].subs(Eq[1]).simplifier()

    Eq << -Eq[-1].reversed

    Eq << Eq[-1] / (2 * x * y * z)

    Eq << cosine_theorem * Eq[4]
    Eq << Eq[-1].expand().subs(Eq[1])
    Eq << Eq[-1].simplifier()

    Eq << Eq[-1] / (x * y * (x + y))

    Eq << Eq[-1] - 1

    Eq << Eq[-1] / -2


if __name__ == '__main__':
    prove(__file__)
