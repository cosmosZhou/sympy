from util import *

from axiom.sets.all_contains.all_contains.all_eq.imply.eq import analyze
# given: ForAll[x:A] (f(x) in B)
#        ForAll[y:B] (g(y) in A)


# |A| = |B|
@apply
def apply(*given):

    all_a, all_b, equality_a, equality_b = given
    A, B, a, b, fa, gb = analyze(all_a, all_b, equality_a)

    eqs = Equal(b, Lambda(a, fa)(gb))
    if equality_b.is_ForAll:
        assert equality_b.variable == b
        assert equality_b.limits == all_b.limits
        equality_b = equality_b.function

    assert equality_b.is_Equal
    assert equality_b == eqs or equality_b.reversed == eqs

    return Equal(Abs(A), Abs(B))


@prove
def prove(Eq):
    from axiom import sets
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
                ForAll[a:A](Equal(a, g(f(a)))), ForAll[b:B](Equal(b, f(g(b)))))

    Eq << sets.all_contains.all_contains.all_eq.imply.eq.apply(Eq[0], Eq[1], Eq[2])

    Eq << sets.all_contains.all_contains.all_eq.imply.eq.apply(Eq[1], Eq[0], Eq[3])

    Eq << sets.eq.eq.imply.eq.abs.apply(Eq[-1], Eq[-2]).reversed


if __name__ == '__main__':
    run()

