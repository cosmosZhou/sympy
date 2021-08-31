from util import *



@apply
def apply(is_imply_P, is_imply_Q):
    p, x = is_imply_P.of(Necessary)
    q, y = is_imply_Q.of(Necessary)

    return Necessary(p & q, x & y)


@prove
def prove(Eq):
    from axiom import algebra
    x, y, a, b = Symbol(real=True, given=True)

    Eq << apply(Necessary(x > 0, a > 0), Necessary(y > 0, b > 0))

    Eq << algebra.necessary.given.necessary.split.et.apply(Eq[-1])

    Eq << Eq[-2].this.rhs.apply(algebra.et.imply.cond, index=0)

    Eq << Eq[-1].this.rhs.apply(algebra.et.imply.cond, index=1)


if __name__ == '__main__':
    run()
