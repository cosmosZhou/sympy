from sympy.core.relational import Unequal, Equality
from axiom.utility import plausible
from sympy.logic.boolalg import Or
from sympy import Symbol
from sympy.concrete.expr_with_limits import ForAll
from sympy.core.function import Function


# given: f(a) != f(b) or a = b
# ForAll[a: a!=b](f(a) != f(b)) 
@plausible
def apply(given, wrt=None):
    assert given.is_Or
    
    for eq in given._argset:            
        if eq.is_Equality:
            if wrt is None:
                if eq.lhs.is_symbol:
                    wrt = eq.lhs
                else:
                    continue
            if not eq._has(wrt):
                continue 
            cond = eq.invert()
            argset = {*given._argset}
            argset.remove(eq)
            return ForAll[wrt:cond](given.func(*argset), given=given)            


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    y = Symbol.y(complex=True, shape=(n,))    
    
    f = Function.f(nargs=(n,), complex=True, shape=())
    g = Function.g(nargs=(n,), complex=True, shape=())

    Eq << apply(Unequal(f(x), g(y)) | Equality(x, y), wrt=x)
    
    Eq << Eq[1].astype(Or)


if __name__ == '__main__':
    prove(__file__)

