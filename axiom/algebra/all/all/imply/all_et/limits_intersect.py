from util import *


@apply
def apply(all_a, all_b):
    from sympy.concrete.limits import limits_intersect
    fn, *limits_a = all_a.of(ForAll)
    _fn, *limits_b = all_b.of(ForAll)

    limits = limits_intersect(limits_a, limits_b)
    return ForAll(fn & _fn, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)

    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(ForAll[e:A](f(e) > 0), ForAll[e:B](g(e) > 0))

    Eq << algebra.all_et.given.all.apply(Eq[-1])

    Eq << algebra.all.given.all.limits.relaxed.apply(Eq[-2], domain=A)

    Eq << algebra.all.given.all.limits.relaxed.apply(Eq[-1], domain=B)


if __name__ == '__main__':
    run()

