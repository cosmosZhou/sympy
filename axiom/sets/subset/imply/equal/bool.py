from axiom.utility import prove, apply
from sympy import Equality, Subset
from sympy import Symbol, Boole
from sympy.core.function import Function
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.symbol import dtype


@apply(imply=True)
def apply(given):
    assert given.is_Subset
    return Equality(Boole(given), 1)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), etype=dtype.real)
    s = Symbol.s(etype=dtype.real)
    
    Eq << apply(Subset(f(x), s))
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    

if __name__ == '__main__':
    prove(__file__)

