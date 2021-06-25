from util import *



@apply
def apply(*given, reverse=False):
    eq, f_eq = given
    assert not f_eq.is_ConditionalBoolean
    (lhs, rhs), *limits = eq.of(All[Equal])
    if reverse:
        lhs, rhs = rhs, lhs
    return All(f_eq._subs(lhs, rhs), *limits)


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

    Eq << apply(All[c:C](Equal(a, f(c))), Contains(a * b + c, S))

    Eq << algebra.cond.all.imply.all_et.apply(Eq[1], Eq[0])

    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs)


if __name__ == '__main__':
    run()
