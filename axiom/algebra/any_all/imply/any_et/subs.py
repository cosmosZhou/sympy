from util import *


@apply
def apply(given, old, new):
    from sympy.concrete.limits import limits_dict
    (function, *limits_f), *limits_e = given.of(Exists[ForAll])
    limits_f_dict = limits_dict(limits_f)

    domain = limits_f_dict[old]
    if domain == []:
        ...
    else:
        assert new in domain

    return Exists(ForAll(function._subs(old, new) & function, *limits_f), *limits_e)


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

    Eq << apply(Exists[C](ForAll[x:A](f(x, C) > 0)), x, x0)

    Eq << Eq[-1].this.function.apply(algebra.all_et.given.et)

    Eq << Eq[0].this.function.apply(algebra.all.imply.et.subs, x, x0)


if __name__ == '__main__':
    run()
