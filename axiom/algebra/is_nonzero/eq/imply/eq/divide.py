from util import *



@apply
def apply(*given):
    is_nonzero, equality = given
    if is_nonzero.is_Equal:
        equality, is_nonzero = given

    x = is_nonzero.of(Unequal[0])
    lhs, rhs = equality.of(Equal)

    return Equal((lhs / x).ratsimp(), (rhs / x).ratsimp())


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    h = Function.h(real=True)

    Eq << apply(Unequal(f(x), 0), Equal(g(x) * f(x), h(x) * f(x) + x))

    Eq << Eq[1] / f(x)

    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

