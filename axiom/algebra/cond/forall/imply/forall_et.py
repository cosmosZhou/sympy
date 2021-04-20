from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(*given):
    cond, forall = given
    if not forall.is_ForAll:
        cond, forall = forall, cond
            
    if cond.is_ConditionalBoolean:
        assert not cond.variables_set & forall.variables_set 
    fn, *limits = axiom.is_ForAll(forall)
    
    return ForAll(cond & fn, *limits)


@prove
def prove(Eq): 
    y = Symbol.y(real=True)
    
    B = Symbol.B(etype=dtype.real)
    
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(f(y) > 0, ForAll[y:B](g(y) > 0))
    
    Eq << algebra.forall_et.given.forall.apply(Eq[-1])
    
    Eq << algebra.forall.given.cond.apply(Eq[-1])
    

if __name__ == '__main__':
    prove()

