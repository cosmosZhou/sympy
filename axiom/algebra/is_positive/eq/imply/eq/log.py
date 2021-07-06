from util import *


@apply
def apply(is_positive, eq):
    den = is_positive.of(Expr > 0)
    lhs, rhs = eq.of(Equal)
    assert den == lhs or den == rhs

    return Equal(log(lhs), log(rhs))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    Eq << apply(f(x) > 0, Equal(f(x), g(x)))

    Eq << Eq[-1].subs(Eq[1])

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[1])

    Eq << algebra.is_positive.imply.is_nonzero.apply(Eq[-1])
    Eq << algebra.is_positive.imply.is_nonzero.apply(Eq[0])


if __name__ == '__main__':
    run()