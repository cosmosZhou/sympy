from axiom.utility import prove, apply
from sympy import Equality, NotContains
from sympy import Symbol, Boole
from sympy.core.function import Function
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.symbol import dtype


@apply(imply=True)
def apply(given):
    assert given.is_NotContains
    return Equality(Boole(given), 1)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    s = Symbol.s(etype=dtype.real)
    
    Eq << apply(NotContains(f(x), s))
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    

if __name__ == '__main__':
    prove(__file__)

