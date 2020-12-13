from axiom.utility import plausible
from sympy import Equality, Supset
from sympy import Symbol, Boole
from sympy.core.function import Function
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.symbol import dtype


@plausible
def apply(given):
    assert given.is_Supset
    return Equality(Boole(given), 1)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), etype=dtype.real)
    s = Symbol.s(etype=dtype.real)
    
    Eq << apply(Supset(f(x), s))
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    

if __name__ == '__main__':
    prove(__file__)

