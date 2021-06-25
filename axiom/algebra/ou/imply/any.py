from util import *


def ou_to_any(imply):
    from sympy.concrete.limits import limits_union
    exists = imply.of(Or)
    fn = set()
    limitsArr = []
    for exist in exists:
        func, *_limits = exist.of(Any)
        fn.add(func)
        assert len(fn) == 1

        limitsArr.append(_limits)

    limits = limitsArr[0]
    for i in range(1, len(limitsArr)):
        limits = limits_union(limits, limitsArr[i])

    fn, *_ = fn
    return Any(fn, *limits)


@apply
def apply(imply):
    return ou_to_any(imply)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real, given=True)
    B = Symbol.B(etype=dtype.real, given=True)

    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Or(Any[x:A]((f(x) > 0)), Any[x:B](f(x) > 0)))

    Eq << ~Eq[1]

    Eq << ~Eq[0]

    Eq << Eq[-1].this.apply(algebra.et.to.all.limits.union)


if __name__ == '__main__':
    run()

