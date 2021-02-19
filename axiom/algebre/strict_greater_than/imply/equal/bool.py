from axiom.utility import prove, apply
from sympy.core.relational import Equality, StrictGreaterThan
from sympy import Symbol, Boole
from sympy.core.function import Function
from sympy.functions.elementary.piecewise import Piecewise


@apply
def apply(given):
    assert given.is_StrictGreaterThan
    return Equality(Boole(given), 1)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(StrictGreaterThan(f(x), y))
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    

if __name__ == '__main__':
    prove(__file__)

