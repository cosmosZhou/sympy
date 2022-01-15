from util import *


@apply
def apply(given):
    fx, fy = given.of(Infer)
    return Assuming(fy, fx)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Infer(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << algebra.assuming.given.ou.apply(Eq[1])

    Eq << algebra.infer.imply.ou.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-03-04
