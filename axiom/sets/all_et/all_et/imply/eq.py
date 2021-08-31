from util import *


@apply
def apply(all_a, all_b):
    (contains_a, equality_a), (a, A) = all_a.of(All[And])
    (contains_b, equality_b), (b, B) = all_b.of(All[And])

    if contains_a.is_Equal:
        equality_a, contains_a = contains_a, equality_a

    if contains_b.is_Equal:
        equality_b, contains_b = contains_b, equality_b

    fa, _B = contains_a.of(Element)
    gb, _A = contains_b.of(Element)
    assert B == _B
    assert A == _A

    assert equality_a.is_Equal and equality_b.is_Equal

    eqs = Equal(a, Lambda(b, gb)(fa))
    assert equality_a == eqs or equality_a.reversed == eqs

    eqs = Equal(b, Lambda(a, fa)(gb))
    assert equality_b == eqs or equality_b.reversed == eqs

    return Equal(Card(A), Card(B))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n, m = Symbol(integer=True, positive=True)

    A = Symbol(etype=dtype.integer * n)
    a = Symbol(integer=True, shape=(n,))

    B = Symbol(etype=dtype.integer * m)
    b = Symbol(integer=True, shape=(m,))

    f = Function(integer=True, shape=(m,))
    g = Function(integer=True, shape=(n,))

    Eq << apply(All[a:A](Element(f(a), B) & Equal(a, g(f(a)))),
                All[b:B](Element(g(b), A) & Equal(b, f(g(b)))))

    Eq << algebra.all_et.imply.et.all.apply(Eq[0])

    Eq << algebra.all_et.imply.et.all.apply(Eq[1])

    Eq << sets.all_el.all_el.all_eq.all_eq.imply.eq.apply(Eq[-3], Eq[-1], Eq[-4], Eq[-2])


if __name__ == '__main__':
    run()

