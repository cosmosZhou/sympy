from util import *


@apply
def apply(eq, contains):
    (ai, (i, n)), X = eq.of(Equal[Cup[FiniteSet, Tuple[0]]])
    _X = n.of(Card)
    assert X == _X

    x, __X = contains.of(Element)
    assert X == _X == __X

    return Any[i:n](Equal(x, ai))


@prove
def prove(Eq):
    from axiom import sets

    X = Symbol(etype=dtype.real, empty=False)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    Eq << apply(Equal(X, a[:Card(X)].set_comprehension()), Element(x, X))

    Eq << Eq[1].subs(Eq[0])
    Eq << sets.el_cup.imply.any_el.apply(Eq[-1])


if __name__ == '__main__':
    run()