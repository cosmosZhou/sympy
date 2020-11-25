from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains
from sympy import Symbol
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import UNION
from sympy.sets.sets import Interval


@plausible
def apply(given, s=None):
    assert given.is_NotContains    
    
    e, S = given.args
    assert S.is_Union
    if s is None:
        s = S.args[0]
    else:
        assert s in S.args
    
    return NotContains(e, s, given=given)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(NotContains(x, A | B))
    
    Eq << Eq[0].split()
    
if __name__ == '__main__':
    prove(__file__)

