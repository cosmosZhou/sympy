from util import *


@apply
def apply(all_is_positive, contains0, contains1, le):
    (fx, (x, d)), (x_, domain) = all_is_positive.of(All[Derivative > 0])
    assert x == x_
    assert d == 1
    assert domain.left_open and domain.right_open
    x0, domain_ = contains0.of(Element)
    assert domain_ == domain

    x1, domain_ = contains1.of(Element)
    assert domain_ == domain

    _x0, _x1 = le.of(Less)
    assert x0 == _x0
    assert x1 == _x1

    f = lambda x: fx._subs(x_, x)
    return f(x0) < f(x1)


@prove
def prove(Eq):
    from axiom import sets

    a, b, x, x0, x1 = Symbol(real=True)
    f = Function(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0), Element(x0, domain), Element(x1, domain), x0 < x1)

    Eq << Eq[0].this.expr.apply(sets.gt.imply.is_extended_real, simplify=None)

    Eq.subset = sets.el.el.imply.subset.interval.apply(Eq[1], Eq[2])

    Eq << sets.subset.all.imply.all.apply(Eq.subset, Eq[-1])

    

    


if __name__ == '__main__':
    run()
