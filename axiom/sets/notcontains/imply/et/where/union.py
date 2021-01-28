from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains
from sympy import Symbol
from sympy.logic.boolalg import And
import axiom


@apply(imply=True)
def apply(given):
    assert given.is_NotContains    
    
    e, S = given.args
    args = axiom.is_Union(S)
    
    eqs = [NotContains(e, s) for s in args]
    
    return And(*eqs)




@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(NotContains(x, A | B))
    
    Eq << Eq[1].split()
    
    Eq << Eq[0].split()

    
if __name__ == '__main__':
    prove(__file__)

