from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Less[Minima])
    return Any(fx < M, *limits)


@prove(provable=False)
def prove(Eq):
    M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Minima[x:Interval(a, b, left_open=True, right_open=True)](f(x)) < M)


if __name__ == '__main__':
    run()
# created on 2019-01-02
# updated on 2021-09-30
