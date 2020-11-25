from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.core.relational import Equality
from sympy import Symbol
from sympy.functions.elementary.complexes import Abs
from sympy.concrete.expr_with_limits import ForAll
from axiom import sets
from sympy.core.function import Lambda, Function
from axiom.sets.forall_contains.forall_contains.forall_equality.imply.equality import analyze
# given: ForAll[x:A] (f(x) in B)
#        ForAll[y:B] (g(y) in A)

 
# |A| = |B|
@plausible
def apply(*given):
    
    forall_a, forall_b, equality_a, equality_b = given
    A, B, a, b, fa, gb = analyze(forall_a, forall_b, equality_a)
    
    eqs = Equality(b, Lambda(a, fa)(gb))
    if equality_b.is_ForAll:
        assert equality_b.variable == b
        assert equality_b.limits == forall_b.limits
        equality_b = equality_b.function
        
    assert equality_b.is_Equal        
    assert equality_b == eqs or equality_b.reversed == eqs        
    
    return Equality(Abs(A), Abs(B), given=given)


from axiom.utility import check


@check
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    A = Symbol.A(etype=dtype.integer * n)
    a = Symbol.a(integer=True, shape=(n,))
    B = Symbol.B(etype=dtype.integer * m)
    b = Symbol.b(integer=True, shape=(m,))
    
    f = Function.f(nargs=(n,), integer=True, shape=(m,))
    g = Function.g(nargs=(m,), integer=True, shape=(n,))

    assert f.is_integer
    assert g.is_integer
    assert f.shape == (m,)
    assert g.shape == (n,)
    
    Eq << apply(ForAll[a:A](Contains(f(a), B)), ForAll[b:B](Contains(g(b), A)),
                ForAll[a:A](Equality(a, g(f(a)))), ForAll[b:B](Equality(b, f(g(b)))))
    
    Eq << sets.forall_contains.forall_contains.forall_equality.imply.equality.apply(Eq[0], Eq[1], Eq[2])
    
    Eq << sets.forall_contains.forall_contains.forall_equality.imply.equality.apply(Eq[1], Eq[0], Eq[3])
        
    Eq << sets.equality.equality.imply.equality.abs.apply(Eq[-1], Eq[-2]).reversed

    
if __name__ == '__main__':
    prove(__file__)

