from util import *



@apply
def apply(given):
    function, *limits = given.of(All)
    assert len(limits) == 1

    limit = limits[0][0], function.invert()

    return All(given.limits_cond.invert().simplify(), limit)


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol(real=True)
    f, g = Function(integer=True)

    Eq << apply(All[e:g(e) > 0](f(e) > 0))

    Eq << algebra.all.imply.ou.apply(Eq[0])

    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=0, wrt=e)


if __name__ == '__main__':
    run()

