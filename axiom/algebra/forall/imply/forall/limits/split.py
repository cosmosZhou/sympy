from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


def split(given, index=-1):
    function, *limits = axiom.is_ForAll(given)
    
    x, s = axiom.limit_is_set(limits)
    
    domain, size = axiom.is_CartesianSpace(s)
    
    x, indices = axiom.is_Slice(x)
        
    start, stop = indices
    assert size == stop - start
    
    if isinstance(index, slice):        
        _start = index.start
        _stop = index.stop
        
        limits = [(x[start:_start], CartesianSpace(domain, _start - start)), 
                  (x[index], CartesianSpace(domain, _stop - start))]
    else:
        if index < 0:
            index += x.shape[0]
        
        limits = [(x[start:index], CartesianSpace(domain, index - start)), (x[index], domain)]
    
        _stop = index + 1
        
    if _stop < stop:
        limits.append((x[_stop:stop], CartesianSpace(domain, stop - _stop)))
                
    return ForAll(function, *limits)

    
@apply
def apply(given, index=-1):
    return split(given, index)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    x = Symbol.x(real=True, shape=(oo,))
    f = Function.f(real=True)

    Eq << apply(ForAll[x[:n + 1]:CartesianSpace(Interval(a, b), n + 1)](f(x[:n + 1]) > 0), index=n)
    
    Eq << algebra.forall.imply.sufficient.apply(Eq[0])
    
    Eq << Eq[-1].this.lhs.apply(algebra.forall.given.et, cond={n})
        
    Eq << algebra.forall.given.sufficient.apply(Eq[1])
        
    Eq << Eq[-1].this.lhs.args[0].simplify()   
    

if __name__ == '__main__':
    prove()

