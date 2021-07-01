from util import *


@apply
def apply(imply):
    from sympy.concrete.limits import limits_cond
    fn, *limits = imply.of(All)
    cond = limits_cond(limits)
    return All(fn & cond, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)
    A = Symbol.A(etype=dtype.integer)

    Eq << apply(All[x:A](f(x) > 0))

    Eq << algebra.all_et.imply.all.apply(Eq[1])


if __name__ == '__main__':
    run()

