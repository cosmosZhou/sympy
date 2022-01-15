from util import *


@apply
def apply(given):
    fx, fy = given.of(Assuming)
    return Infer(fy, fx)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Assuming(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << algebra.infer.imply.assuming.reverse.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-03-04
