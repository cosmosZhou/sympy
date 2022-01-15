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

    n = Symbol(integer=True, positive=True)
    x, x0, a = Symbol(real=True)
    #x = Symbol.x(real=True, shape=(n,))
    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    #x0 = Symbol.x0(real=True, shape=(n,))
    x0 = oo
    #x0 = -oo
    #a = oo
    #a = -oo
    direction = 1
    Eq << apply(Element(Limit[x:x0:direction](f(x)), Reals), var='A')

    Eq << calculus.is_limited.imply.any_all.limit_definition.apply(Eq[0])

    Eq << Eq[-1].subs(Eq[1].reversed)


if __name__ == '__main__':
    run()
# created on 2020-04-08
