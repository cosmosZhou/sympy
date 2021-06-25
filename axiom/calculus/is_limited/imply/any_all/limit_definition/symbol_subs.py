from util import *


@apply
def apply(given, ε=None, δ=None, var=None):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    fn, (x, x0, dir), *R = of_limited(given)
#     A = given.generate_var(definition=given)

    A = fn.generate_var(excludes={x}, **fn.type.dict)

    cond = any_all(Equal(given.lhs, A), ε, δ)
    B = fn.generate_var(excludes={x}, definition=given.lhs, var=var)
    return cond._subs(A, B)


@prove
def prove(Eq):
    from axiom import calculus
    n = Symbol.n(integer=True, positive=True)

    x = Symbol.x(real=True)
#     x = Symbol.x(real=True, shape=(n,))
    x = Symbol.x(integer=True)

    f = Function.f(real=True, shape=())

    x0 = Symbol.x0(real=True)
#     x0 = Symbol.x0(real=True, shape=(n,))

    x0 = oo
#     x0 = -oo

    a = Symbol.a(real=True)
#     a = oo
#     a = -oo

    direction = 1

    Eq << apply(Contains(Limit[x:x0:direction](f(x)), Reals), var='A')

    Eq << calculus.is_limited.imply.any_all.limit_definition.apply(Eq[1])

    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
