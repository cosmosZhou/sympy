from util import *



@apply
def apply(*given):
    all_A, all_B = given
    assert all_A.is_ForAll and all_B.is_ForAll
    assert len(all_A.limits) == len(all_B.limits) == 1
    x, A = all_A.limits[0]
    _x, B = all_B.limits[0]
    assert x == _x
    assert A.is_ConditionSet or A.definition.is_ConditionSet
    assert B.is_ConditionSet or B.definition.is_ConditionSet
    assert all_A.function == B.image_set()[-1]
    assert all_B.function == A.image_set()[-1]

    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    f = Function.f(nargs=(n,), integer=True, shape=())
    g = Function.g(nargs=(n,), integer=True, shape=())
    A = Symbol.A(conditionset(x, Equal(f(x), 1)))
    B = Symbol.B(conditionset(x, Equal(g(x), 1)))

    assert f.is_integer and g.is_integer
    assert f.shape == g.shape == ()

    Eq << apply(ForAll[x:A](Equal(g(x), 1)), ForAll[x:B](Equal(f(x), 1)))
    Eq << sets.imply.all.conditionset.apply(A)

    Eq << sets.imply.all.conditionset.apply(B)

    Eq << ForAll[x:A](Contains(x, B), plausible=True)

    Eq << Eq[-1].this.function.rhs.definition

    Eq << ForAll[x:B](Contains(x, A), plausible=True)

    Eq << Eq[-1].this.function.rhs.definition

    Eq << sets.all_contains.all_contains.imply.eq.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

