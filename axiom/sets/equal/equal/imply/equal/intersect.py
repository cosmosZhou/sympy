from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy.core.function import Function
from sympy import UNION
from sympy.functions.elementary.complexes import Abs
from axiom import sets
import axiom


@apply
def apply(*given):
    equality_A, equality_B = given
    a, b = axiom.is_Equal(equality_A)    
    x, y = axiom.is_Equal(equality_B)
    
    return Equality(a & x, b & y)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(etype=dtype.integer * n)
    B = Symbol.B(etype=dtype.integer * n)
    X = Symbol.X(etype=dtype.integer * n)    
    Y = Symbol.Y(etype=dtype.integer * n)
    
    Eq << apply(Equality(A, B), Equality(X, Y))
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-1].subs(Eq[1])
    

if __name__ == '__main__':
    prove(__file__)

