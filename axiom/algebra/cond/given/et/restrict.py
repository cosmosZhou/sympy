from util import *


@apply
def apply(imply, *, cond=None):
    return And(imply, cond)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(f(x) < 0, cond=g(x) > 0)

    Eq << algebra.et.imply.cond.apply(Eq[1], index=0)


if __name__ == '__main__':
    run()

