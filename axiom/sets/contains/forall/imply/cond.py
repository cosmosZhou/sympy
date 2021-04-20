from sympy import *
from axiom.utility import prove, apply
from axiom import algebra


# given: A in B 
# => A | B = B
@apply
def apply(*given):
    contains, forall = given
    assert contains.is_Contains and forall.is_ForAll
    b, A = contains.args
   
    index = -1
    for i, (x, *domain) in enumerate(forall.limits):
        if len(domain) == 1:
            if domain[0] == A:
                index = i
                break
                
    assert index >= 0        
            
    function = forall.function
    function = function._subs(x, b) if x != b else function
    limits = [*forall.limits]
    del limits[index]
    if limits:
        return ForAll(function, *limits)
    
    return function


@prove
def prove(Eq):
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    a = Symbol.a(complex=True, shape=(n,))    
    b = Symbol.b(complex=True, shape=(n,))
    
    f = Function.f(nargs=(n,), complex=True, shape=())

    assert f.is_complex
    assert f.shape == ()
    
    Eq << apply(Contains(b, A), ForAll[a:A](Equal(f(a), 1)))
    
    Eq << algebra.forall.imply.ou.subs.apply(Eq[1], a, b)
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])


if __name__ == '__main__':
    prove()

