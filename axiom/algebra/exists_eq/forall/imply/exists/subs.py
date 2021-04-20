from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given, reverse=False):
    exists_eq, forall = given
    
    fn, *limits = axiom.exists_eq(exists_eq)
    cond, *_limits = axiom.is_ForAll(forall)   
    assert limits == _limits
    
    x, y = fn.args
    if reverse:
        x, y = y, x
    return Exists(cond._subs(x, y), *limits)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Exists[x:S](Equal(g(x), f(x))), ForAll[x:S](g(x) > y))
    
    Eq << algebra.forall.exists.imply.exists_et.apply(Eq[0], Eq[1])
    
    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs)

    
if __name__ == '__main__':
    prove()

