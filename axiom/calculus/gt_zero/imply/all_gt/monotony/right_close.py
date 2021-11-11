from util import *


@apply
def apply(given):
    fx, (x, n) = given.of(Derivative > 0)
    assert n == 1

    domain = x.domain

    assert not domain.left_open and not domain.right_open
    a, b = domain.of(Interval)

    return All[x:Interval(a, b, left_open=True)](Greater(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    a, b = Symbol(real=True)
    x = Symbol(domain=Interval(a, b))
    f = Function(real=True)
    Eq << apply(Derivative[x](f(x)) > 0)

    Eq << algebra.cond.imply.all.apply(Eq[0], x)

    Eq << calculus.all_gt_zero.imply.all_gt.monotony.right_close.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-06-02
# updated on 2020-06-02
