from util import *


@apply
def apply(given):
    fx, (x, n) = given.of(Derivative <= 0)
    assert n == 1

    domain = x.domain

    a, b = domain.of(Interval)
    assert not domain.right_open

    return GreaterEqual(fx, fx._subs(x, b))


@prove(proved=False)
def prove(Eq):
    a, b = Symbol(real=True)

    x = Symbol(domain=Interval(a, b))

    f = Function(real=True)

    Eq << apply(Derivative[x](f(x)) <= 0)


if __name__ == '__main__':
    run()
# created on 2021-07-29
# updated on 2021-07-29
