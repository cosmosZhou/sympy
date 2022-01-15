from util import *


@apply
def apply(a, b):
    return Subset(a.set & b.set, Interval(a, b))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x, y)





    Eq << Eq[0].this.lhs.apply(sets.intersect_finiteset.to.piece)

    Eq << algebra.cond.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.eq)


if __name__ == '__main__':
    run()
# created on 2018-09-11
