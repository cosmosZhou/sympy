from util import *


@apply
def apply(lt, gt):
    x, m = gt.of(Greater)
    _x, M = lt.of(Less)
    assert x == _x

    return Less(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from axiom import algebra

    x, m, M = Symbol(real=True, given=True)
    Eq << apply(x < M, x > m)

    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=x >= 0)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[0].apply(algebra.cond.imply.et.ou, cond=x >= 0)

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << algebra.ou.imply.ou.invert.apply(Eq[-2])

    Eq << Eq[-1].this.args[0].apply(algebra.is_nonnegative.lt.imply.lt.square)

    Eq << Eq[-1].this.args[1].apply(algebra.lt.imply.lt.relax, Eq[2].rhs)

    Eq << Eq[1].apply(algebra.cond.imply.et.ou, cond=x > 0)

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << algebra.ou.imply.ou.invert.apply(Eq[-2])

    Eq << Eq[-1].this.args[0].apply(algebra.is_nonpositive.gt.imply.lt.square)

    Eq << Eq[-1].this.args[1].apply(algebra.lt.imply.lt.relax, Eq[2].rhs)

    Eq << Eq[-1].this.args[0].apply(algebra.gt.imply.ge.relax)


if __name__ == '__main__':
    run()