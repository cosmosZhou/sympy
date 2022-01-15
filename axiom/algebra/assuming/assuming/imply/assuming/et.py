from util import *



@apply
def apply(is_imply_P, is_imply_Q):
    p, x = is_imply_P.of(Assuming)
    q, y = is_imply_Q.of(Assuming)

    return Assuming(p & q, x & y)


@prove
def prove(Eq):
    from axiom import algebra
    x, y, a, b = Symbol(real=True, given=True)

    Eq << apply(Assuming(x > 0, a > 0), Assuming(y > 0, b > 0))

    Eq << algebra.assuming.given.assuming.split.et.apply(Eq[-1])

    Eq << Eq[-2].this.rhs.apply(algebra.et.imply.cond, index=0)

    Eq << Eq[-1].this.rhs.apply(algebra.et.imply.cond, index=1)


if __name__ == '__main__':
    run()
# created on 2018-03-28
