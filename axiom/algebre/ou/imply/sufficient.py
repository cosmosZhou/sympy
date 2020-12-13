from sympy.core.relational import Unequal, Equality
from axiom.utility import plausible
from sympy import Symbol, Or
from sympy import ForAll
from sympy.core.function import Function
import axiom
from axiom import sets, algebre
from sympy.functions.special.tensor_functions import Boole
from sympy.sets.contains import Contains
from sympy.functions.elementary.piecewise import Piecewise
from sympy.logic.boolalg import Sufficient


# given: f(a) != f(b) or a = b
# ForAll[a: a!=b](f(a) != f(b)) 
@plausible
def apply(given, pivot=0):
    conds = axiom.is_Or(given)
    
    eq = conds.pop(pivot)
    
    cond = eq.invert()
    
    return Sufficient(cond, given.func(*conds))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    y = Symbol.y(complex=True, shape=(n,))    
    
    f = Function.f(nargs=(n,), complex=True, shape=())
    g = Function.g(nargs=(n,), complex=True, shape=())

    Eq << apply(Unequal(f(x), g(y)) | Equality(x, y), pivot=1)
    
    Eq << Eq[1].astype(Or)
    
if __name__ == '__main__':
    prove(__file__)

