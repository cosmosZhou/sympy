from util import *


@apply
def apply(*given):
    A, B, a, b, fa, gb = analyze(*given)

    return Equal(Cup[b:B](gb.set), A)


def analyze(*given):
    all_a, all_b, equality_a = given

    assert all_a.is_ForAll and all_b.is_ForAll
    assert len(all_a.variables) == len(all_b.variables) == 1
    a = all_a.variable
    b = all_b.variable

    assert all_a.function.is_Contains and all_b.function.is_Contains

    B = all_a.function.rhs
    A = all_b.function.rhs

    fa = all_a.function.lhs
    gb = all_b.function.lhs
    assert fa._has(a) and gb._has(b)

    eqs = Equal(a, Lambda(b, gb)(fa))
    if equality_a.is_ForAll:
        assert equality_a.variable == a
        assert equality_a.limits == all_a.limits
        equality_a = equality_a.function

    assert equality_a.is_Equal
    assert equality_a == eqs or equality_a.reversed == eqs

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

    Eq << apply(ForAll[a:A](Contains(f(a), B)), ForAll[b:B](Contains(g(b), A)),
                ForAll[a:A](Equal(a, g(f(a)))))

    Eq << Eq[1].this.function.apply(sets.contains.imply.subset, simplify=False)

    Eq.subset_A = sets.all_subset.imply.subset.cup.lhs.apply(Eq[-1])

    Eq.supset_A = Eq.subset_A.func.reversed_type(*Eq.subset_A.args, plausible=True)

    Eq << sets.supset.given.all_contains.apply(Eq.supset_A, var=Eq[0].variable)

    Eq << Eq[-1].this.function.apply(sets.contains.given.any_eq.split.imageset)

    Eq <<= Eq[-1] & Eq[2]

    Eq << Eq[-1].this.function.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.all_et.given.all.apply(Eq[-1])

    Eq << ForAll[a:A](Exists[b:B](Equal(f(a), b)), plausible=True)

    Eq << Eq[-1].this.function.simplify()

    Eq << Eq[-1].this.function.function.apply(algebra.eq.imply.eq.invoke, g)

    Eq <<= Eq.supset_A & Eq.subset_A


if __name__ == '__main__':
    run()

