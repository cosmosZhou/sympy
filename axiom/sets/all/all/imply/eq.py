from util import *


@apply
def apply(all_A, all_B):
    A_function, (x, A) = all_A.of(All)
    B_function, (_x, B) = all_B.of(All)
    
    assert A_function == B.image_set()[-1]
    assert B_function == A.image_set()[-1]
        
    assert x == _x
    assert A.is_ConditionSet or A.definition.is_ConditionSet
    assert B.is_ConditionSet or B.definition.is_ConditionSet

    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    f = Function.f(integer=True, shape=())
    g = Function.g(integer=True, shape=())
    A = Symbol.A(conditionset(x, Equal(f(x), 1)))
    B = Symbol.B(conditionset(x, Equal(g(x), 1)))

    assert f.is_integer and g.is_integer
    assert f.shape == g.shape == ()

    Eq << apply(All[x:A](Equal(g(x), 1)), All[x:B](Equal(f(x), 1)))
    Eq << sets.imply.all.conditionset.apply(A)

    Eq << sets.imply.all.conditionset.apply(B)

    Eq << All[x:A](Contains(x, B), plausible=True)

    Eq << Eq[-1].this.function.rhs.definition

    Eq << All[x:B](Contains(x, A), plausible=True)

    Eq << Eq[-1].this.function.rhs.definition

    Eq << sets.all_contains.all_contains.imply.eq.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
