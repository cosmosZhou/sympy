from sympy import *
from axiom.utility import prove, apply
import axiom


@apply
def apply(imply, s):
    function, *limits = axiom.is_ForAll(imply)
    x, cond, baseset = axiom.limit_is_baseset(limits)
    assert s.is_Symbol
    _x, _cond, _baseset = axiom.is_ConditionSet(s.definition)
    assert x == _x
    assert _cond == cond
    assert _baseset == baseset    
    
    return ForAll[x:s](function)


@prove
def prove(Eq): 
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    S = Symbol.S(etype=dtype.complex * n)
    f = Function.f(nargs=(n,), shape=(), integer=True)
    g = Function.g(nargs=(n,), shape=(), integer=True)
    
    s = Symbol.s(conditionset(x, Equal(f(x), 1), S))
    Eq << apply(ForAll[x: Equal(f(x), 1):S](Equal(g(x), 1)), s)    
    
    Eq << Eq[-1].this.limits[0][1].definition


if __name__ == '__main__':
    prove()
