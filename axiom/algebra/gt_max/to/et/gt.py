from util import *


@apply(given=None)
def apply(given, index=-1):
    x, args = given.of(Greater[Expr, Max])
    if index is None:
        eqs = [x > arg for arg in args]
    else:
        first = args[:index]
        second = args[index:]
        eqs = x > Max(*first), x > Max(*second)
        
    return Equivalent(given, And(*eqs), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x > Max(y, z))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.gt_max.imply.et.gt)

    Eq << Eq[-1].this.rhs.apply(algebra.gt.gt.imply.gt.max.rhs)

    


if __name__ == '__main__':
    run()
# created on 2022-01-01
