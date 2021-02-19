from sympy import *
from axiom.utility import prove, apply
from axiom import sets
from sympy.sets.conditionset import conditionset


@apply
def apply(*given):
    forall_A, forall_B = given
    assert forall_A.is_ForAll and forall_B.is_ForAll
    assert len(forall_A.limits) == len(forall_B.limits) == 1
    x, A = forall_A.limits[0]
    _x, B = forall_B.limits[0]
    assert x == _x
    assert A.is_ConditionSet or A.definition.is_ConditionSet 
    assert B.is_ConditionSet or B.definition.is_ConditionSet
    assert forall_A.function == B.image_set()[-1]
    assert forall_B.function == A.image_set()[-1]

    return Equality(A, B)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    f = Function.f(nargs=(n,), integer=True, shape=())
    g = Function.g(nargs=(n,), integer=True, shape=())
    A = Symbol.A(definition=conditionset(x, Equality(f(x), 1)))
    B = Symbol.B(definition=conditionset(x, Equality(g(x), 1)))
    
    assert f.is_integer and g.is_integer
    assert f.shape == g.shape == ()
    
    Eq << apply(ForAll[x:A](Equality(g(x), 1)), ForAll[x:B](Equality(f(x), 1)))
    Eq << sets.imply.forall.conditionset.apply(A)
    
    Eq << sets.imply.forall.conditionset.apply(B)
    
    Eq << ForAll[x:A](Contains(x, B), plausible=True)
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq << ForAll[x:B](Contains(x, A), plausible=True)
    
    Eq << Eq[-1].this.function.rhs.definition

    Eq << sets.forall_contains.forall_contains.imply.equal.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    prove(__file__)

