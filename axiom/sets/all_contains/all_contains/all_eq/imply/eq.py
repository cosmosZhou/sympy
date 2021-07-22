from util import *


@apply
def apply(*given):
    A, B, a, b, fa, gb = analyze(*given)

    return Equal(Cup[b:B](gb.set), A)


def analyze(*given):
    all_a, all_b, equality_a = given

    (fa, B), (a, _A) = all_a.of(All[Contains])
    (gb, A), (b, _B) = all_b.of(All[Contains])
    
    assert _A == A
    assert _B == B    
    assert fa._has(a) and gb._has(b)

    eqs = Equal(a, Lambda(b, gb)(fa))
    if equality_a.is_All:
        equality_a, limit = equality_a.of(All)
        assert limit == (a, A)

    assert {*equality_a.of(Equal)} == {*eqs.args}

    return A, B, a, b, fa, gb


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    A = Symbol.A(etype=dtype.integer * n)
    a = Symbol.a(integer=True, shape=(n,))
    B = Symbol.B(etype=dtype.integer * m)
    b = Symbol.b(integer=True, shape=(m,))
    f = Function.f(integer=True, shape=(m,))
    g = Function.g(integer=True, shape=(n,))
    Eq << apply(All[a:A](Contains(f(a), B)), All[b:B](Contains(g(b), A)),
                All[a:A](Equal(a, g(f(a)))))

    Eq << Eq[1].this.expr.apply(sets.contains.imply.subset, simplify=False)

    Eq.subset_A = sets.all_subset.imply.subset.cup.lhs.apply(Eq[-1])

    Eq.supset_A = Eq.subset_A.func.reversed_type(*Eq.subset_A.args, plausible=True)

    Eq << sets.supset.given.all_contains.apply(Eq.supset_A, var=Eq[0].variable)

    Eq << Eq[-1].this.expr.apply(sets.contains.given.any_eq.split.imageset)

    Eq <<= Eq[-1] & Eq[2]

    Eq << Eq[-1].this.expr.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.all_et.given.all.apply(Eq[-1])

    Eq << All[a:A](Any[b:B](Equal(f(a), b)), plausible=True)

    Eq << Eq[-1].this.expr.simplify()

    Eq << Eq[-1].this.expr.expr.apply(algebra.eq.imply.eq.invoke, g)

    Eq <<= Eq.supset_A & Eq.subset_A


if __name__ == '__main__':
    run()

