from util import *


@apply
def apply(*given):
    from sympy.concrete.limits import limits_dependent
    forall, exists = given
    fx, *limits_f = forall.of(ForAll)
    fy, *limits_e = exists.of(Exists)

    assert not limits_dependent(limits_f, limits_e)
    return Exists(ForAll(fx & fy, *limits_f), *limits_e)


@prove
def prove(Eq):
    from axiom import algebra
    y = Symbol.y(real=True)
    x = Symbol.x(real=True)
    z = Symbol.z(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    h = Function.h(integer=True)

    Eq << apply(ForAll[z:h(z) > 0](h(y, z) > 0), Exists[y:g(y) > 1, x:f(x) > 0](g(x) > 0))

    Eq << Eq[-1].this.function.apply(algebra.all_et.given.et)

#     Eq << Eq[-1].this.find(ForAll).apply(algebra.all.given.cond)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()

