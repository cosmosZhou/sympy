from sympy import *
from axiom.utility import prove, apply

from sympy.sets.conditionset import conditionset
import axiom


@apply(given=True)
def apply(imply):
    function, *limits = axiom.is_ForAll(imply)
    x, cond, baseset = axiom.limit_is_baseset(limits)
    conditionset(x, cond, baseset)
    
    return ForAll[x:conditionset(x, cond, baseset)](function)


@prove
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    S = Symbol.S(etype=dtype.complex * n)
    f = Function.f(nargs=(n,), shape=(), integer=True)
    g = Function.g(nargs=(n,), shape=(), integer=True)
    
    Eq << apply(ForAll[x: Equality(f(x), 1) :S](Equality(g(x), 1)))
    
    Eq << Eq[1].simplify()

if __name__ == '__main__':
    prove(__file__)
