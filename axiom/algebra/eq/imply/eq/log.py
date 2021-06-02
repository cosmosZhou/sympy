from util import *
import axiom


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    assert lhs.is_nonzero
    assert rhs.is_nonzero

    return Equal(log(lhs), log(rhs))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True, positive=True)
    g = Function.g(shape=(), real=True, positive=True)

    Eq << apply(Equal(f(x), g(x)))

    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], log)


if __name__ == '__main__':
    run()
