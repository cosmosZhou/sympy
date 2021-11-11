from util import *


@apply
def apply(is_nonpositive, lt, left_open=True, right_open=True, x=None):
    _M = is_nonpositive.of(Expr <= 0)
    m, M = lt.of(Less)
    assert M == _M
    if x is None:
        x = lt.generate_var(real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, M ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(M <= 0, m < M, x=x)

    Eq << algebra.imply.eq.inf.st.even_function.apply(x ** 2, Eq[2].find(Interval), x)












    Eq <<= -Eq[0], -Eq[1].reversed

    Eq << algebra.ge_zero.lt.imply.eq.inf_square.to.square.apply(Eq[-2], Eq[-1])

    Eq << Eq[-4].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()
# created on 2019-12-08
# updated on 2019-12-08
