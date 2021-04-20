from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(*given):
    cond, exists = given
    if not exists.is_Exists:
        cond, exists = exists, cond
    
    if cond.is_ConditionalBoolean:
        assert not cond.variables_set & exists.variables_set
        
    fn, *limits = axiom.is_Exists(exists)
    
    return Exists(cond & fn, *limits)


@prove
def prove(Eq): 
    y = Symbol.y(real=True)
    
    B = Symbol.B(etype=dtype.real, given=True)
    
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(f(y) > 0, Exists[y:B](g(y) > 0))
    
    Eq << ~Eq[-1].simplify()
    
    Eq << algebra.forall.exists.imply.exists_et.apply(Eq[-1], Eq[1])
    
    Eq << algebra.exists_et.imply.exists.split.apply(Eq[-1], index=0)
    
    Eq << ~Eq[-1]
    
    Eq << algebra.cond.imply.forall.restrict.apply(Eq[0], (y, B))
    

if __name__ == '__main__':
    prove()

