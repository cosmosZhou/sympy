from util import *


@apply
def apply(given): 
    ((fx, M), *limits), (M, M0_domain) = given.of(All[Any[Greater]])
    a, M0 = M0_domain.of(Interval)
    assert a.is_NegativeInfinity and M0_domain.right_open
    return Sup(fx, *limits) >= M0


@prove
def prove(Eq):
    M0 = Symbol(real=True, given=True)
    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[M:Interval(-oo, M0, right_open=True)](Any[x:a:b](f(x) > M)))


if __name__ == '__main__':
    run()