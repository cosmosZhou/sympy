from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Slice, Max
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype


@apply(imply=True)
def apply(given, x):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equality(Max(lhs, x).simplify(), Max(rhs, x).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    
    Eq << apply(Equality(x, y), z)    
    
    Eq << Eq[-1].subs(Eq[0])
        

if __name__ == '__main__':
    prove(__file__)

