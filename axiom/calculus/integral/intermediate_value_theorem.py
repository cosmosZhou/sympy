
from sympy.core.numbers import oo
from axiom.utility import plausible
from sympy.core.relational import Equality
from sympy import Symbol

from sympy.concrete.expr_with_limits import Exists, ForAll, MAX, MIN

from sympy.sets.sets import Interval
from sympy.core.function import Function


@plausible
def apply(given):
    assert given.is_ForAll
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

    y = Symbol.y(real=True)
    return ForAll(Exists(Equality(f, y), (z, a, b)),
            (y, MIN(f, (z, a, b)), MAX(f, (z, a, b))),
            given=given)               


from axiom.utility import check


@check
def prove(Eq):    

    a = Symbol.a(real=True)
    b = Symbol.b(real=True, domain=Interval(a, oo, left_open=True))

    Eq << apply(Equality.continuity(Function('f'), a, b))


if __name__ == '__main__':
    prove(__file__)

