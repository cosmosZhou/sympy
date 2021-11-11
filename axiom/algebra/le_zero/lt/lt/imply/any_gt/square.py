from util import *


@apply
def apply(M_is_nonpositive, lt_mM, lt, x=None):
    _M = M_is_nonpositive.of(Expr <= 0)
    m, M = lt_mM.of(Less)
    assert _M == M

    U, M2 = lt.of(Less)
    _m = M2.of(Expr ** 2)
    assert _m == m
    if x is None:
        x = lt.generate_var(real=True)
    return Any[x:Interval(m, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from axiom import algebra

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(M <= 0, m < M, U < m ** 2)

    Eq << -Eq[0]

    Eq << -Eq[1].reversed

    Eq << algebra.ge_zero.lt.lt.imply.any_gt.square.apply(Eq[-2], Eq[-1], Eq[2])

    x = Eq[-1].variable
    Eq << algebra.any.imply.any.limits.subs.negate.real.apply(Eq[-1], x, -x)


if __name__ == '__main__':
    run()
# created on 2019-07-07
# updated on 2019-07-07
