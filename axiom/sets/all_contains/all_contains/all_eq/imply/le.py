from util import *

from axiom.sets.all_contains.all_contains.all_eq.imply.eq import analyze
# given: ForAll[x:A] (f(x) in B)
#        ForAll[y:B] (g(y) in A)


# |A| = |B|
@apply
def apply(*given):
    A, B, a, b, fa, gb = analyze(*given)
    return LessEqual(Abs(A), Abs(B))


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
                ForAll[a:A](Equal(a, g(f(a)))))

    Eq << sets.all_contains.all_contains.all_eq.imply.eq.apply(Eq[0], Eq[1], Eq[2])

    Eq << sets.imply.le.cup.apply(*Eq[-1].lhs.args)

    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    run()

