from util import *



@apply
def apply(given):
    assert given.is_ForAll
    limits = given.limits
    assert len(limits) == 1

    limit = limits[0][0], given.function.invert()

    return ForAll(given.limits_cond.invert().simplify(), limit)


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(ForAll[e:g(e) > 0](f(e) > 0))

    Eq << algebra.all.imply.ou.apply(Eq[0])

    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=0, wrt=e)


if __name__ == '__main__':
    run()

