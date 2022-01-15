from util import *


@apply
def apply(given, index=0):
    from sympy.concrete.limits import limits_cond
    assert index == 0
    function, *limits = given.of(All)

    assert len(limits) > 1

    limit, *limits = limits
    cond = limits_cond((limit,))
    return All(function | cond.invert(), *limits)


@prove
def prove(Eq):
    from axiom import algebra
    A, B = Symbol(etype=dtype.real)
    x, y = Symbol(real=True)
    f = Function(real=True)

    Eq << apply(All[x:A, y:B](f(x, y) > 0))

    Eq << Eq[1].this.expr.apply(algebra.ou.imply.all, pivot=1)


if __name__ == '__main__':
    run()

# created on 2018-12-12
