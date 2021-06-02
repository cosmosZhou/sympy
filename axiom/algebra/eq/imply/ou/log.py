from util import *
import axiom



@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    return Or(Equal(log(lhs), log(rhs)), Equal(lhs, 0))


@prove
def prove(Eq):
    from axiom import algebra
    b = Symbol.b(real=True)
    a = Symbol.a(real=True)
    x = Symbol.x(domain=Interval(a, b))
    f = Function.f(real=True)
    g = Function.g(real=True)

    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[1].subs(Eq[0])

    Eq << algebra.ou.given.et.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[0].reversed)

    # the following codes will issue an error because of illegal domain definition
#     Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], log)


if __name__ == '__main__':
    run()

