from util import *


@apply
def apply(given, *limits):

    function, *limits_f = given.of(All)

    variables_set = given.variables_set
    for var, *ab in limits:
        assert var not in variables_set

    limits = tuple(limits_f) + limits
    return All(function, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    A, B = Symbol(etype=dtype.real)
    x, y = Symbol(real=True)
    f = Function(real=True)

    Eq << apply(All[x:A](f(x, y) > 0), (y, B))

    Eq << Eq[0].this.expr.apply(algebra.cond.imply.all.restrict, (y, B))

    Eq << algebra.all.imply.all.limits.swap.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-12-14
# updated on 2018-12-14
