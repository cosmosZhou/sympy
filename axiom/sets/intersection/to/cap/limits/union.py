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
    k = Symbol.k(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    f = Function.f(etype=dtype.integer)
    Eq << apply(Intersection(Cap[k:A](f(k)), Cap[k:B](f(k)), evaluate=False))

    Eq << Eq[0].this.find(Cap).apply(sets.cap.piecewise)

    Eq << Eq[-1].this.lhs.find(Cap).apply(sets.cap.piecewise)

    Eq << Eq[-1].this.lhs.find(Cap).apply(sets.cap.piecewise)

    Eq << Eq[-1].this.lhs.apply(sets.intersection.to.cap)

    Eq << Eq[-1].this.lhs.expr.apply(sets.intersection.to.piecewise)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.piecewise.flatten)


if __name__ == '__main__':
    run()
