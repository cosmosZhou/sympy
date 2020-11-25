from axiom.utility import plausible
from sympy.core.relational import Unequal, Equality, Equal
from sympy import Symbol
import axiom
from sympy.logic.boolalg import Or
from axiom import algebre
from sympy.functions.special.tensor_functions import KroneckerDelta


@plausible
def apply(given, var=None):
    lhs, rhs = axiom.is_Unequal(given)
    if var is None:
        var = given.generate_free_symbol(**lhs.type.dict)
    return Equal(KroneckerDelta(lhs, var) * KroneckerDelta(rhs, var), 0, given=given)


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True)
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequal(x, y), k)
    Eq << ~Eq[-1]
        
    Eq << Eq[-1].apply(algebre.is_nonzero.imply.et)

    Eq << Eq[-1].apply(algebre.is_nonzero.imply.equality.kronecker_delta, algebre.is_nonzero.imply.equality.kronecker_delta)

    Eq << Eq[-1].split()[0]
    
    Eq <<= Eq[-1] & Eq[0]
    
    


if __name__ == '__main__':
    prove(__file__)
