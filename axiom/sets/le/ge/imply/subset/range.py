from util import *


@apply
def apply(greater_than, _greater_than):
    x, a = greater_than.of(LessEqual)
    y, b = _greater_than.of(GreaterEqual)

    assert x.is_integer and y.is_integer and a.is_integer and b.is_integer
    return Subset(Range(y, x + 1), Range(b, a + 1))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x, y = Symbol(integer=True, given=True)
    Eq << apply(y <= b, x >= a)

    Eq << sets.subset.given.all_el.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(sets.notin_range.imply.ou)

    Eq << algebra.any.imply.any_et.limits.single_variable.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1].apply(sets.el_range.imply.et)

    #if self implies a False proposition, then self must be False
    Eq << Eq[-1].this.expr.apply(algebra.cond.cond.ou.given.ou, simplify=False)

    Eq.any_ax, Eq.any_by = Any(Eq[-1].expr.args[0], *Eq[-1].limits, plausible=True), Any(Eq[-1].expr.args[1], *Eq[-1].limits, plausible=True)

    Eq <<= algebra.any_et.imply.any.limits_absorb.apply(Eq.any_ax, index=1), algebra.any_et.imply.any.limits_absorb.apply(Eq.any_by, index=2)

    Eq <<= Eq[-2].this.expr.apply(algebra.lt.ge.imply.lt.transit), Eq[-1].this.expr.apply(algebra.lt.ge.imply.gt.transit)

    Eq <<= Eq[-2] & Eq[1], Eq[-1] & Eq[0]

    Eq << ~(~Eq.any_ax & ~Eq.any_by)


if __name__ == '__main__':
    run()

# created on 2021-05-18
