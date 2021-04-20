from axiom.utility import prove, apply
from sympy import *
from axiom import algebra
import axiom


@apply
def apply(given): 
    forall_a, forall_b = axiom.is_And(given)
    fn, *limits = axiom.is_ForAll(forall_a) 
    _fn, *_limits = axiom.is_ForAll(forall_b)
    assert limits == _limits
    return ForAll(fn & _fn, *limits)


@prove
def prove(Eq):
    e = Symbol.e(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    h = Function.h(integer=True)

    Eq << apply(And(ForAll[e:g(e) > 0](f(e) > 0), ForAll[e:g(e) > 0](h(e) > 0)))
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[1])
    
    Eq << algebra.et.given.cond.apply(Eq[0])
    

if __name__ == '__main__':
    prove()

