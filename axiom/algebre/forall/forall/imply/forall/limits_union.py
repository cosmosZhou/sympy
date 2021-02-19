from axiom.utility import prove, apply
from sympy import *
from axiom import algebre
import axiom
from sympy.concrete.limits import limits_union


@apply
def apply(*given):
    forall_a, forall_b = given
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

    Eq << apply(ForAll[e:g(e) > 0](f(e) > 0), ForAll[e:g(e) < 0](f(e) > 0))
    
    Eq <<= Eq[0] & Eq[1]
    
    

if __name__ == '__main__':
    prove(__file__)

