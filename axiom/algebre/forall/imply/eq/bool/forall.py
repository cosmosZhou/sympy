from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Boole
from sympy.core.function import Function
from sympy.functions.elementary.piecewise import Piecewise


@apply
def apply(given):
    assert given.is_ForAll
    return Equality(Boole(given), 1)




@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    f = Function.f(nargs=(), shape=(), integer=True)
    s = Symbol.s(etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)
    
    Eq << apply(ForAll[x:A](Contains(f(x), s)))
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    

if __name__ == '__main__':
    prove(__file__)

