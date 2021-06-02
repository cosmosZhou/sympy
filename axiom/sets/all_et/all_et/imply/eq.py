from util import *


@apply
def apply(all_a, all_b):
    (contains_a, equality_a), (a, A) = all_a.of(ForAll[And])
    (contains_b, equality_b), (b, B) = all_b.of(ForAll[And])

    if contains_a.is_Equal:
        equality_a, contains_a = contains_a, equality_a

    if contains_b.is_Equal:
        equality_b, contains_b = contains_b, equality_b

    fa, _B = contains_a.of(Contains)
    gb, _A = contains_b.of(Contains)
    assert B == _B
    assert A == _A

    assert equality_a.is_Equal and equality_b.is_Equal

    eqs = Equal(a, Lambda(b, gb)(fa))
    assert equality_a == eqs or equality_a.reversed == eqs

    eqs = Equal(b, Lambda(a, fa)(gb))
    assert equality_b == eqs or equality_b.reversed == eqs

    return Equal(Abs(A), Abs(B))


@prove
def prove(Eq):
    from axiom import sets, algebra
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

    Eq << apply(ForAll[a:A](Contains(f(a), B) & Equal(a, g(f(a)))),
                ForAll[b:B](Contains(g(b), A) & Equal(b, f(g(b)))))

    Eq << algebra.all_et.imply.all.apply(Eq[0])

    Eq << algebra.all_et.imply.all.apply(Eq[1])

    Eq << sets.all_contains.all_contains.all_eq.all_eq.imply.eq.apply(Eq[-3], Eq[-1], Eq[-4], Eq[-2])


if __name__ == '__main__':
    run()

