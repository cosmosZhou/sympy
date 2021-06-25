from util import *


@apply
def apply(*given, reverse=False):
    eq, f_eq = given
    (lhs, rhs), *limits_f = eq.of(All[Equal])
    f_eq, *limits_e = f_eq.of(Any)

    assert limits_f == limits_e
    if reverse:
        lhs, rhs = rhs, lhs

    return Any(f_eq._subs(lhs, rhs), *limits_f)


@prove
def prove(Eq):
    from axiom import algebra
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)

    a = Symbol.a(real=True, shape=(m, n))
    b = Symbol.b(real=True, shape=(m, n))
    c = Symbol.c(real=True, shape=(m, n))

    f = Function.f(real=True)

    C = Symbol.C(etype=dtype.real * (m, n))
    S = Symbol.S(etype=dtype.real * (m, n))

    Eq << apply(All[c:C](Equal(a, f(c))), Any[c:C](Contains(a * b + c, S)))

    Eq << algebra.all.any.imply.any_et.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs)


if __name__ == '__main__':
    run()
