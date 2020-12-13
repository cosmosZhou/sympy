from sympy.core.relational import Equality, Unequal
from axiom.utility import plausible

from sympy import Symbol

from sympy.core.function import Function
import axiom

from sympy import Or
from sympy.logic.boolalg import And


@plausible
def apply(given, *, factor=None):
    or_eqs = axiom.is_Or(given)
    
    new_or_eqs = []
    
    and_eqs = []
    for and_eq in or_eqs:
        if and_eq.is_And:
            try:
                i = and_eq.args.index(factor)
                args = [*and_eq.args]
                del args[i]
                and_eqs.append(And(*args))
                continue
            except:
                ...
        new_or_eqs.append(and_eq)
        
    if and_eqs:        
        new_or_eqs.append(And(Or(*and_eqs), factor))            
        return Or(*new_or_eqs)


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    
    f = Function.f(nargs=(k,), shape=(k,), real=True)
    h = Function.h(nargs=(k,), shape=(k,), real=True)
    g = Function.g(nargs=(k,), shape=(k,), real=True)
    
    Eq << apply(Unequal(x, y) | Equality(f(x), g(y)) & (y > 0) | Equality(h(x), g(y)) & (y > 0), factor=y > 0)
    
    Eq << Eq[1].this.args[0].astype(Or)


if __name__ == '__main__':
    prove(__file__)

