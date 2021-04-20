from sympy import *
from axiom.utility import prove, apply
from axiom import sets
from axiom import algebra
# given: ForAll[a:A] (f(a) in B)
#        ForAll[b:B] (g(b) in A)


def analyze(*given):
    forall_a, forall_b, equality_a = given
        
    assert forall_a.is_ForAll and forall_b.is_ForAll
    assert len(forall_a.variables) == len(forall_b.variables) == 1
    a = forall_a.variable
    b = forall_b.variable
    
    assert forall_a.function.is_Contains and forall_b.function.is_Contains
    
    B = forall_a.function.rhs
    A = forall_b.function.rhs
    
    fa = forall_a.function.lhs
    gb = forall_b.function.lhs
    assert fa._has(a) and gb._has(b)
    
    eqs = Equal(a, Lambda(b, gb)(fa))
    if equality_a.is_ForAll:
        assert equality_a.variable == a
        assert equality_a.limits == forall_a.limits
        equality_a = equality_a.function

    assert equality_a.is_Equal
    assert equality_a == eqs or equality_a.reversed == eqs
        
    return A, B, a, b, fa, gb


# |A| = |B|
@apply
def apply(*given): 
    A, B, a, b, fa, gb = analyze(*given)
    
    return Equal(UNION[b:B](gb.set), A)


@prove
def prove(Eq): 
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    A = Symbol.A(etype=dtype.integer * n)
    a = Symbol.a(integer=True, shape=(n,))
    B = Symbol.B(etype=dtype.integer * m)
    b = Symbol.b(integer=True, shape=(m,))
    
    f = Function.f(integer=True, shape=(m,))
    g = Function.g(integer=True, shape=(n,))

    Eq << apply(ForAll[a:A](Contains(f(a), B)), ForAll[b:B](Contains(g(b), A)),
                ForAll[a:A](Equal(a, g(f(a)))))
    
    Eq << Eq[1].this.function.apply(sets.contains.imply.subset, simplify=False)
        
    Eq.subset_A = sets.forall_subset.imply.subset.union_comprehension.lhs.apply(Eq[-1])
    
    Eq.supset_A = Eq.subset_A.func.reversed_type(*Eq.subset_A.args, plausible=True)
    
    Eq << sets.supset.given.forall_contains.apply(Eq.supset_A)
    
    Eq << Eq[-1].this.function.apply(sets.contains.given.exists_eq.split.imageset)
    
    Eq <<= Eq[-1] & Eq[2]
    
    Eq << Eq[-1].this.function.apply(algebra.et.given.et.subs.eq)
    
    Eq << algebra.forall_et.given.forall.apply(Eq[-1])
    
    Eq << ForAll[a:A](Exists[b:B](Equal(f(a), b)), plausible=True)
    
    Eq << Eq[-1].this.function.simplify()
    
    Eq << Eq[-1].this.function.function.apply(algebra.eq.imply.eq.invoke, g)
    
    Eq <<= Eq.supset_A & Eq.subset_A

            
if __name__ == '__main__':
    prove()

