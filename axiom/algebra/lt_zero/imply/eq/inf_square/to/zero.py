from util import *


@apply
def apply(given, x):
    m = given.of(Expr < 0)
    return Equal(Inf[x:Interval(m, 0, left_open=True, right_open=True)](x ** 2), 0)


@prove
def prove(Eq):
    from axiom import algebra

    m, x = Symbol(real=True)
    Eq << apply(m < 0, x)

    Eq << algebra.imply.eq.inf.st.even_function.apply(x ** 2, Eq[1].find(Interval), x)












    Eq << -Eq[0]

    Eq << algebra.gt_zero.imply.eq.inf_square.to.zero.apply(Eq[-1], x=x)

    Eq << Eq[-3].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()
# created on 2019-12-21
# updated on 2019-12-21
