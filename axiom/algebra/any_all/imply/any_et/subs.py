from util import *


@apply
def apply(given, old, new):
    from sympy.concrete.limits import limits_dict
    (function, *limits_f), *limits_e = given.of(Any[All])
    limits_f_dict = limits_dict(limits_f)

    domain = limits_f_dict[old]
    if domain:
        assert new in domain

    return Any(All(function._subs(old, new) & function, *limits_f), *limits_e)


@prove
def prove(Eq):
    from axiom import algebra

    C = Symbol.C(real=True)
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    x0 = Symbol.x0(domain=A)
    f = Function.f(integer=True)
    Eq << apply(Any[C](All[x:A](f(x, C) > 0)), x, x0)

    Eq << Eq[-1].this.expr.apply(algebra.all_et.given.et.all)

    Eq << Eq[-1].this.find(Or).apply(algebra.ou.given.cond, 1)

    Eq << Eq[0].this.expr.apply(algebra.cond.imply.et.invoke, algebra.all.imply.cond.subs, x, x0)


if __name__ == '__main__':
    run()
