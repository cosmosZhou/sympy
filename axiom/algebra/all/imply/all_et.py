from util import *


@apply
def apply(given, index=None):
    from sympy.concrete.limits import limits_cond
    fn, *limits = given.of(ForAll)

    if index is None:
        cond = limits_cond(limits)
    else:
        if isinstance(index, slice):
            cond = limits_cond(limits[index])
        else:
            cond = limits_cond([limits[index]])
    return ForAll(fn & cond, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)

    Eq << apply(ForAll[x:g(x) > 0](f(x) > 0))

    Eq << algebra.all_et.given.all.apply(Eq[-1])


if __name__ == '__main__':
    run()

