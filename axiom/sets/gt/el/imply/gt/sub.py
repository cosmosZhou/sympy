from util import *


@apply(simplify=False)
def apply(le, el):
    a, b = le.of(Greater)
    t, s = el.of(Element)
    assert s in Interval(-oo, oo)
    return Greater(a - t, b - t)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y, a, b = Symbol(real=True, given=True)
    t = Symbol(hyper_real=True, given=True)
    Eq << apply(x > y, Element(t, Interval(a, b)))

    Eq << sets.el.imply.el.relax.apply(Eq[1], Reals, simplify=None)

    z = Symbol(real=True)
    Eq << sets.el.imply.any_eq.apply(Eq[-1], var=z)

    Eq << Eq[0] - z

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)


if __name__ == '__main__':
    run()