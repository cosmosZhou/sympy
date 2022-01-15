from util import *


@apply(simplify=False)
def apply(given, index=None):
    from sympy.concrete.limits import limits_cond
    fn, *limits = given.of(All)

    if index is None:
        cond = limits_cond(limits)
    else:
        if isinstance(index, slice):
            cond = limits_cond(limits[index])
        else:
            cond = limits_cond([limits[index]])
    return All(fn & cond, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(All[x:g(x) > 0](f(x) > 0))

    Eq << algebra.all_et.given.et.all.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-12-17
