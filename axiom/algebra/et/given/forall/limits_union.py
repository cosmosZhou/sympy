from axiom.utility import prove, apply
from sympy import *
from axiom import algebra
import axiom
from sympy.concrete.limits import limits_union


@apply
def apply(given):    
    forall_a, forall_b = axiom.is_And(given)
    fn, *limits_a = axiom.is_ForAll(forall_a) 
    _fn, *limits_b = axiom.is_ForAll(forall_b)
    assert fn == _fn
    limits = limits_union(limits_a, limits_b)
    return ForAll(fn, *limits)


@prove
def prove(Eq):
    e = Symbol.e(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(And(ForAll[e:g(e) > 0](f(e) > 0), ForAll[e:g(e) < 0](f(e) > 0)))
    
    Eq << algebra.forall.imply.et.split.apply(Eq[1], cond=g(e) < 0)
    
    

if __name__ == '__main__':
    prove()

