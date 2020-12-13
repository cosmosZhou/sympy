
from axiom.utility import plausible
from sympy.core.symbol import dtype

from sympy import Symbol
from sympy import Exists
from sympy.sets.contains import Contains


@plausible
def apply(given):
    assert given.is_Exists
    limit, *limits = given.limits
    assert len(limit) == 1
    x = limit[0]
    assert given.function.is_Contains
    _x, S = given.function.args
    assert x == _x
    return Exists(Contains(x, S), (x, S), *limits)


from axiom.utility import check


@check
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    t = Symbol.t(real=True)

    Eq << apply(Exists[e, t:S](Contains(e, S - {t})))
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[0].simplify()


if __name__ == '__main__':
    prove(__file__)

