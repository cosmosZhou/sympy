from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
# given: ForAll[x:A] (f(x) in B)
#        ForAll[y:B] (g(y) in A)

 
# |A| = |B|
@apply
def apply(*given):
    
    forall_a, forall_b = given
    assert len(forall_a.limits) == len(forall_b.limits) == 1
    a, A = forall_a.limits[0]
    b, B = forall_b.limits[0]
    
    assert forall_a.function.is_And
    assert forall_b.function.is_And
    contains_a, equality_a = forall_a.function.args
    if contains_a.is_Equality:
        equality_a, contains_a = contains_a, equality_a
        
    contains_b, equality_b = forall_b.function.args
    if contains_b.is_Equality:
        equality_b, contains_b = contains_b, equality_b
        
    assert contains_a.is_Contains and contains_b.is_Contains
    assert equality_a.is_Equality and equality_b.is_Equality
    
    fa, _B = contains_a.args
    assert B == _B
    gb, _A = contains_b.args
    assert A == _A
    
    eqs = Equality(a, Lambda(b, gb)(fa))
    assert equality_a == eqs or equality_a.reversed == eqs
    
    eqs = Equality(b, Lambda(a, fa)(gb))
    assert equality_b == eqs or equality_b.reversed == eqs        
    
    return Equality(Abs(A), Abs(B))


@prove
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
    
    Eq << apply(ForAll[a:A](Contains(f(a), B) & Equality(a, g(f(a)))),
                ForAll[b:B](Contains(g(b), A) & Equality(b, f(g(b)))))

    Eq << algebre.forall_et.imply.forall.apply(Eq[0])
    
    Eq << algebre.forall_et.imply.forall.apply(Eq[1])
    
    Eq << sets.forall_contains.forall_contains.forall_eq.forall_eq.imply.eq.apply(Eq[-3], Eq[-1], Eq[-4], Eq[-2])

    
if __name__ == '__main__':
    prove(__file__)

