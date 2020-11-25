from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.core.relational import Equality
from sympy import Symbol
from sympy.core.function import Function
from sympy.concrete.expr_with_limits import ForAll


# given: A in B 
# => A | B = B
@plausible
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
        return ForAll(function, *limits, given=given)
    
    return function.copy(given=given)

from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    a = Symbol.a(complex=True, shape=(n,))    
    b = Symbol.b(complex=True, shape=(n,))
    
    f = Function.f(nargs=(n,), complex=True, shape=())

    assert f.is_complex
    assert f.shape == ()
    
    Eq << apply(Contains(b, A), ForAll[a:A](Equality(f(a), 1)))
    
    Eq << Eq[1].subs(a, b)
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq << Eq[-1].split()


if __name__ == '__main__':
    prove(__file__)

