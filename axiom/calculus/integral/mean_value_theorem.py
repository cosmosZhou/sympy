from sympy.core.symbol import Symbol
from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality

from sympy.concrete.expr_with_limits import Exists, Minimum, Maximum
from sympy.integrals.integrals import Integral
from sympy.sets.sets import Interval
from sympy.core.function import Function
import axiom


@plausible
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

    return Exists(Equality(Integral(f, (z, a, b)), (b - a) * _f), limit, given=given)


from sympy.utility import check


@check
def prove(Eq):    

    a = Symbol('a', real=True)
    b = Symbol('b', real=True, domain=Interval(a, oo, left_open=True))

    assert b > a 
    assert b - a > 0
    
    f = Function('f')
    given = Equality.continuity(f, a, b)
    
    z = given.lhs.args[1]

    Eq << apply(given)
    
    m = Symbol('m', definition=Minimum(f(z), (z, a, b)))
    M = Symbol('M', definition=Maximum(f(z), (z, a, b)))
    
    Eq.min, Eq.max = m.equality_defined(), M.equality_defined()
    
    Eq << axiom.calculus.integral.intermediate_value_theorem.apply(given)
    
    Eq.intermediate_value = Eq[-1].this.limits[0][2].subs(Eq.max.reversed).this.limits[0][1].subs(Eq.min.reversed)
    
    Eq << m.definition.assertion().integral((z, a, b)).subs(Eq.min.reversed) / (b - a) 
    
    Eq << M.definition.assertion().integral((z, a, b)).subs(Eq.max.reversed) / (b - a)
    
    Eq << (Eq[-1] & Eq[-2])
#     Eq << (Eq[-1].reversed & Eq[-2])
#     Eq << (Eq[-1] & Eq[-2].reversed)
#     Eq << (Eq[-1].reversed & Eq[-2].reversed)
#     Eq << (Eq[-2] & Eq[-1])
#     Eq << (Eq[-2].reversed & Eq[-1])
#     Eq << (Eq[-2] & Eq[-1].reversed)
#     Eq << (Eq[-2].reversed & Eq[-1].reversed)
         
    Eq << Eq.intermediate_value.subs(Eq.intermediate_value.rhs, Eq[-1].lhs)
    
    Eq << (Eq[-1] & Eq[-2]) 
    
    Eq << Eq[-1].split()
    
    Eq << Eq[-1] * (b - a)
    
    Eq << Eq[-1].this.function.rhs.ratsimp().reversed
    
    Eq << Eq[1].subs(Eq[1].variable, z)
    
#     Eq << Eq[-1].rewrite(index=1)

    
if __name__ == '__main__':
    prove(__file__)

