from util import *


@apply
def apply(forall, exists):
    from sympy.concrete.limits import limits_dependent
    fx, *limits_f = forall.of(All)
    fy, *limits_e = exists.of(Any)

    assert not limits_dependent(limits_f, limits_e)
    return Any(All(fx & fy, *limits_f), *limits_e)


@prove
def prove(Eq):
    from axiom import algebra

    y = Symbol.y(real=True)
    x = Symbol.x(real=True)
    z = Symbol.z(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    h = Function.h(integer=True)
    Eq << apply(All[z:h(z) > 0](h(y, z) > 0), Any[y:g(y) > 1, x:f(x) > 0](g(x) > 0))

    Eq << Eq[-1].this.expr.apply(algebra.all_et.given.et.all)

    Eq << Eq[-1].this.find(Or).apply(algebra.ou.given.cond, 0)

    
    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()

