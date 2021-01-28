from sympy.core.relational import Equality, Unequal
from axiom.utility import prove, apply

from sympy import Symbol

from sympy.core.function import Function
import axiom

from sympy import Or
from sympy.logic.boolalg import And

@apply(imply=True)
def apply(given, pivot=0):
    or_eqs = axiom.is_Or(given)
    
    precondition = or_eqs[pivot]
    del or_eqs[pivot]
    statement = Or(*or_eqs)
    
    return Or(precondition, precondition.invert() & statement)            




@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    
    f = Function.f(nargs=(k,), shape=(k,), real=True)
    g = Function.g(nargs=(k,), shape=(k,), real=True)
    
    Eq << apply(Unequal(x, y) | Equality(f(x), g(y)), pivot=1)
    
    Eq << Eq[-1].astype(And)


if __name__ == '__main__':
    prove(__file__)

