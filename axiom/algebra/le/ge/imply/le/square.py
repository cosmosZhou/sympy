from util import *


@apply
def apply(greater_than, less_than):
    x, m = greater_than.of(GreaterEqual)
    _x, M = less_than.of(LessEqual)
    assert x == _x

    return LessEqual(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from axiom import algebra

    x, m, M = Symbol(real=True, given=True)
    Eq << apply(x >= m, x <= M)

    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=x >= 0)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[1].apply(algebra.cond.imply.et.ou, cond=x >= 0)

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << algebra.ou.imply.ou.invert.apply(Eq[-2])

    Eq << Eq[-1].this.args[0].apply(algebra.ge_zero.le.imply.le.square)

    Eq << Eq[-1].this.args[1].apply(algebra.le.imply.le.relax, Eq[2].rhs)

    Eq << Eq[0].apply(algebra.cond.imply.et.ou, cond=x > 0)

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << algebra.ou.imply.ou.invert.apply(Eq[-2])

    Eq << Eq[-1].this.args[0].apply(algebra.le_zero.ge.imply.le.square)

    Eq << Eq[-1].this.args[1].apply(algebra.le.imply.le.relax, Eq[2].rhs)

    Eq << Eq[-1].this.args[0].apply(algebra.gt.imply.ge.relax)


if __name__ == '__main__':
    run()
# created on 2019-10-25
# updated on 2019-10-25
