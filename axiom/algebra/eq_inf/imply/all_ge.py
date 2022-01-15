from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Equal[Inf])
    return All(fx >= M, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    M, x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Equal(M, Inf[x:S](f(x))))

    Eq << algebra.imply.le.inf_min.apply(Eq[0].rhs)

    Eq << Eq[-1].subs(Eq[0].reversed).reversed

    Eq << algebra.minima_ge.imply.all_ge.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-01-04
