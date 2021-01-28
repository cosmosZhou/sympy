from axiom.utility import prove, apply

from sympy import *
from axiom import sets


@apply(imply=True)
def apply(*given):
    subset, forall = given
    if subset.is_ForAll:
        forall, subset = subset, forall
    assert subset.is_Subset and forall.is_ForAll
    B, A = subset.args
   
    index = -1
    for i, (x, *domain) in enumerate(forall.limits):
        if len(domain) == 1:
            if domain[0] == A:
                index = i
                break
                
    assert index >= 0        
            
    function = forall.function
    limits = [*forall.limits]
    limits[index] = (x, B)
    return ForAll(function, *limits)




@prove
def prove(Eq):
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    x = Symbol.x(complex=True, shape=(n,))    
    
    f = Function.f(nargs=(n,), complex=True, shape=())

    assert f.is_complex
    assert f.shape == ()
    
    Eq << apply(Subset(B, A), ForAll[x:A](Equality(f(x), 1)))
    
    Eq << Eq[0].definition
    
    Eq << Eq[-1].limits_subs(Eq[-1].variable, x)
    
    Eq << Eq[-1].apply(sets.contains.forall.imply.condition, Eq[1], join=False)


if __name__ == '__main__':
    prove(__file__)

