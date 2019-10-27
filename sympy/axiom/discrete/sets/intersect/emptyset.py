from sympy.core.relational import Equality, LessThan
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy.axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains
from sympy.concrete.expr_with_limits import Exists
from sympy.logic.boolalg import plausibles


# given e not in S
def apply(provided):

    e, s = provided.args
    return Equality(e.set & s, S.EmptySet,
                    equivalent=provided,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    s = Symbol('s', dtype=dtype.integer)
    e = Symbol('e', integer=True)

    provided = NotContains(e, s)
    Eq << provided
    Eq << apply(provided)

    Eq << Eq[-1].lhs.assertion()

    Eq << Eq[-1].split()

    Eq << Eq[-1].split()

    Eq << Eq[-1].this.function.simplifier()

    Eq << Eq[-1].subs(Eq[-1].limits[0][0], e)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << (Eq[-1] & Eq[0])

    Eq << (Eq[2] & (~Eq[3])).split()


if __name__ == '__main__':
    prove(__file__)

