from util import *


@apply
def apply(ceil):
    x = ceil.of(Ceiling)

    return Equal(ceil, -floor(-x))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    Eq << apply(ceiling(x))

    Eq << algebra.cond.given.suffice.bisected.apply(Eq[-1], cond=Contains(x, Integers))

    Eq << Eq[-2].this.lhs.apply(sets.contains.imply.any_eq)

    Eq << Eq[-1].this.lhs.function.apply(algebra.cond.imply.et.invoke, algebra.eq.imply.eq.ceiling)

    Eq << -Eq[-1].this.lhs.function.args[0]

    Eq << Eq[-1].this.lhs.function.args[0].apply(algebra.eq.imply.eq.floor)

    Eq << Eq[-1].this.lhs.function.apply(algebra.eq.eq.imply.eq.add)

    Eq << Eq[-1].this.rhs.apply(algebra.eq.given.is_zero)

    Eq << Eq[2].this.lhs.apply(algebra.cond.imply.et.invoke, sets.notcontains.imply.eq.ceiling)

    Eq << Eq[-1].this.lhs.args[0].apply(sets.notcontains.imply.eq.floor_frac)

    Eq << Eq[-1].this.find(frac).apply(algebra.frac.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.eq.eq.imply.eq.add)


if __name__ == '__main__':
    run()
