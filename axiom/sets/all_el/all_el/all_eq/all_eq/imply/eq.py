from util import *


@apply
def apply(all_a, all_b, equality_a, equality_b):
    from axiom.sets.all_el.all_el.all_eq.imply.eq import analyze
    A, B, a, b, fa, gb = analyze(all_a, all_b, equality_a)

    eqs = Equal(b, Lambda(a, fa)(gb))
    if equality_b.is_ForAll:
        assert equality_b.variable == b
        assert equality_b.limits == all_b.limits
        equality_b = equality_b.expr

    assert equality_b.is_Equal
    assert equality_b == eqs or equality_b.reversed == eqs

    return Equal(Card(A), Card(B))


@prove
def prove(Eq):
    from axiom import sets
    n, m = Symbol(integer=True, positive=True)
    A = Symbol(etype=dtype.integer * n)
    a = Symbol(integer=True, shape=(n,))

    B = Symbol(etype=dtype.integer * m)
    b = Symbol(integer=True, shape=(m,))

    f = Function(integer=True, shape=(m,))
    g = Function(integer=True, shape=(n,))

    Eq << apply(All[a:A](Element(f(a), B)), All[b:B](Element(g(b), A)),
                All[a:A](Equal(a, g(f(a)))), All[b:B](Equal(b, f(g(b)))))

    Eq << sets.all_el.all_el.all_eq.imply.eq.apply(Eq[0], Eq[1], Eq[2])

    Eq << sets.all_el.all_el.all_eq.imply.eq.apply(Eq[1], Eq[0], Eq[3])

    Eq << sets.eq.eq.imply.eq.card.apply(Eq[-1], Eq[-2]).reversed


if __name__ == '__main__':
    run()

# created on 2020-07-31
