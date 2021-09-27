from util import *


@apply
def apply(given, sgm):
    A, B = given.of(Equal[Intersection, EmptySet])
    fx, (x, s) = sgm.of(Sum)
    _A, _B = s.of(Union)
    assert A == _A and B == _B

    return Equal(sgm, Sum[x:A](fx).simplify() + Sum[x:B](fx).simplify())


@prove
def prove(Eq):
    from axiom import algebra, sets

    A, B = Symbol(etype=dtype.integer)
    x = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Equal(Intersection(A, B), A.etype.emptySet), Sum[x:A | B](f(x)))

    Eq << algebra.sum.to.add.split.apply(Eq[1].lhs, cond=B)

    Eq << sets.intersect_is_empty.imply.eq.complement.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
