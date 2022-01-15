from util import *

from axiom.sets.union.to.cup.limits.union import limits_union


@apply
def apply(self):
    A, B = self.of(Intersection)
    function, *limits_a = A.of(Cap)
    _function, *limits_b = B.of(Cap)
    assert function == _function

    limits = limits_union(limits_a, limits_b, function=function)
    return Equal(self, Cap(function, *limits), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, algebra
    k = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    f = Function(etype=dtype.integer)
    Eq << apply(Intersection(Cap[k:A](f(k)), Cap[k:B](f(k)), evaluate=False))

    Eq << Eq[0].this.find(Cap).apply(sets.cap.piece)

    Eq << Eq[-1].this.lhs.find(Cap).apply(sets.cap.piece)

    Eq << Eq[-1].this.lhs.find(Cap).apply(sets.cap.piece)

    Eq << Eq[-1].this.lhs.apply(sets.intersect.to.cap)

    Eq << Eq[-1].this.lhs.expr.apply(sets.intersect.to.piece)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.piece.flatten)


if __name__ == '__main__':
    run()
# created on 2021-04-28
