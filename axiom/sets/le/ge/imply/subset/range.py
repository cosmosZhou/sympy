from util import *


@apply
def apply(*given):
    greater_than, _greater_than = given
    x, a = greater_than.of(LessEqual)
    y, b = _greater_than.of(GreaterEqual)

    assert x.is_integer and y.is_integer and a.is_integer and b.is_integer
    return Subset(Range(y, x + 1), Range(b, a + 1))


@prove
def prove(Eq):
    from axiom import sets, algebra
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)

    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)

    Eq << apply(y <= b, x >= a)

    Eq << sets.subset.given.all_contains.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.function.apply(sets.notcontains.imply.ou.split.range)

    Eq << algebra.any.imply.any_et.single_variable.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.function.args[1].apply(sets.contains.imply.et.split.range)

    # if self implies a False proposition, then self must be False
    Eq << Eq[-1].this.function.apply(algebra.et.given.ou, simplify=False)

    Eq.any_ax, Eq.any_by = Exists(Eq[-1].function.args[0], *Eq[-1].limits, plausible=True), Exists(Eq[-1].function.args[1], *Eq[-1].limits, plausible=True)

    Eq <<= algebra.any_et.imply.any.limits_absorb.apply(Eq.any_ax, index=1), algebra.any_et.imply.any.limits_absorb.apply(Eq.any_by, index=2)

    Eq <<= Eq[-2].this.function.apply(algebra.lt.ge.imply.lt.transit), Eq[-1].this.function.apply(algebra.lt.ge.imply.gt.transit)

    Eq <<= Eq[-2] & Eq[1], Eq[-1] & Eq[0]

    Eq << ~(~Eq.any_ax & ~Eq.any_by)


if __name__ == '__main__':
    run()

