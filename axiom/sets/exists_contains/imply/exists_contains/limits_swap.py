
from axiom.utility import plausible
from sympy.core.symbol import dtype

from sympy import Symbol
from sympy.concrete.expr_with_limits import Exists
from sympy.sets.contains import Contains


@plausible
def apply(given):
    assert given.is_Exists
    assert len(given.limits) == 1
    limit = given.limits[0]
    x, A = limit
    assert given.function.is_Contains
    _x, B = given.function.args
    assert x == _x
    return Exists[x:B](Contains(x, A), given=given)


from axiom.utility import check


@check
def prove(Eq):
    
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    e = Symbol.e(real=True)

    Eq << apply(Exists[e:A](Contains(e, B)))
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[0].simplify()


if __name__ == '__main__':
    prove(__file__)

