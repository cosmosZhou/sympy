from sympy.core.symbol import Symbol
from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality

from sympy.concrete.expr_with_limits import Exists, Forall, Maximum, Minimum

from sympy.sets.sets import Interval
from sympy.core.function import Function


def apply(given):
    assert given.is_Forall
    assert given.function.is_Equality
    assert given.function.lhs.is_Limit
    f, z, xi, direction = given.function.lhs.args
    assert direction.name == '+-'
    assert len(given.limits) == 1
    limit = given.limits[0]
    _xi, a, b = limit
    assert xi == _xi
    _f = f._subs(z, xi)
    assert given.function.rhs == _f

    y = Symbol('y', real=True)
    return Forall(Exists(Equality(f, y), (z, a, b)),
            (y, Minimum(f, (z, a, b)), Maximum(f, (z, a, b))),
            given=given,
            plausible=plausible())               


from sympy.utility import check


@check
def prove(Eq):    

    a = Symbol('a', real=True)
    b = Symbol('b', real=True, domain=Interval(a, oo, left_open=True))

    given = Equality.continuity(Function('f'), a, b)

    Eq << given

    Eq << apply(given)


if __name__ == '__main__':
    prove(__file__)

