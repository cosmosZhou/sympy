from util import *


@apply
def apply(imply):
    lhs, rhs = imply.of(Equal)
    return Equal(exp(lhs), exp(rhs))

@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[1].apply(algebra.eq.imply.eq.log)


if __name__ == '__main__':
    run()