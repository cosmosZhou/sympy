from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given, reverse=False):
    forall_exists, cond = given
    assert not cond.is_ConditionalBoolean
    (fn, *limits_e), *limits_f = axiom.forall_exists(forall_exists)
    
    x, y = axiom.is_Equal(fn)
    if reverse:
        x, y = y, x
        
    return ForAll(Exists(cond._subs(x, y), *limits_e), *limits_f)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(ForAll[y:B](Exists[x:A](Equal(g(x, y), f(x, y)))), g(x, y) > y)
    
    Eq << algebra.cond.forall.imply.forall_et.apply(Eq[1], Eq[0])
    
    Eq << Eq[-1].this.function.apply(algebra.exists_eq.cond.imply.exists.subs)

    
if __name__ == '__main__':
    prove()

