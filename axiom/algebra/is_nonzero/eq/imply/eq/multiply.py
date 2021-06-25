from util import *



@apply
def apply(*given):
    is_nonzero, equality = given
    if is_nonzero.is_Equal:
        equality, is_nonzero = given

    x = is_nonzero.of(Unequal[0])
    lhs, rhs = equality.of(Equal)

    return Equal((x * lhs).expand(), (x * rhs).expand())


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    h = Function.h(real=True)

    Eq << apply(Unequal(f(x), 0), Equal(g(x) / f(x), h(x) / f(x) + x))

    Eq << Eq[-1] / f(x)

    Eq << ~Eq[-1]

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << ~Eq[0]

    Eq << ~Eq[1]

if __name__ == '__main__':
    run()



