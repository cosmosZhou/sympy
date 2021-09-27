from util import *


@apply
def apply(lt, left_open=True, right_open=True, x=None):
    m, M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, Max(m ** 2, M ** 2))


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x=x)

    Eq << algebra.eq.given.et.squeeze.apply(Eq[-1])

    Eq << Element(x, Interval(m, M, left_open=True, right_open=True)).this.apply(sets.el_interval.imply.lt.square)

    Eq << algebra.suffice.imply.all.apply(Eq[-1])

    Eq << algebra.all_lt.imply.le_sup.apply(Eq[-1])

    Eq << algebra.ge_sup.given.all_any_gt.apply(Eq[3], 'U')

    Eq << algebra.all.given.suffice.apply(Eq[-1])

    Eq << algebra.cond.imply.suffice.et.apply(Eq[0], cond=Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.lt.lt_max.imply.any_gt.square)


if __name__ == '__main__':
    run()