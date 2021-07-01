from util import *


@apply
def apply(a, b):    
    return Subset(a.set & b.set, Interval(a, b))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x, y)

    

    

    Eq << Eq[0].this.lhs.apply(sets.intersection_finiteset.to.piecewise)

    Eq << algebra.cond.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.eq)


if __name__ == '__main__':
    run()