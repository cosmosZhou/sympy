from util import *


def split_all(given, cond, wrt):
    from axiom.algebra.sum.to.add.split import split

    if isinstance(cond, Boolean):
        if wrt is None:
            wrt = cond.wrt

        cond = wrt.domain_conditioned(cond)

        if wrt not in given.variables:
            domain = given.domain_defined(wrt)
            function, *limits = given.of(All)
            given = All(function, *limits, (wrt, domain))

    return split(All, given, cond, wrt=wrt)


@apply
def apply(given, *, cond=None, wrt=None):
    given = split_all(given, cond, wrt)
    return given.of(And)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    f = Function(integer=True, shape=())
    d = Symbol(real=True, positive=True)
    #for x > 0
    #Eq << apply(All[x:-d:d](f(x) > 0), cond=x > 0)
    #
    #Eq << algebra.et.given.et.apply(Eq[-1])
    #
    #Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(0, d, left_open=True))
    #
    #Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(-d, 0))
    #for x >= 0
    #Eq << apply(All[x:-d:d](f(x) > 0), cond=x >= 0)
    #
    #Eq << algebra.et.given.et.apply(Eq[-1])
    #
    #Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(0, d))
    #
    #Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(-d, 0, right_open=True))
    #for x < 0
    #Eq << apply(All[x:-d:d](f(x) > 0), cond=x < 0)
    #
    #Eq << algebra.et.given.et.apply(Eq[-1])
    #
    #Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(0, d))
    #
    #Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(-d, 0, right_open=True))
    #for x:(-d,d), x < 0
    Eq << apply(All[x:Interval(-d, d, left_open=True, right_open=True)](f(x) > 0), cond=x < 0)

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(0, d, right_open=True))

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(-d, 0, right_open=True, left_open=True))

    #for x <= 0
    #Eq << apply(All[x:-d:d](f(x) > 0), cond=x <= 0)
    #
    #Eq << algebra.et.given.et.apply(Eq[-1])
    #
    #Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(0, d, left_open=True))
    #
    #Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(-d, 0))
    #for x in (-d, d) cond = x <= 0
    #Eq << apply(All[x:Interval(-d, d, left_open=True, right_open=True)](f(x) > 0), cond=x <= 0)
    #
    #Eq << algebra.et.given.et.apply(Eq[-1])
    #
    #Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(0, d, left_open=True, right_open=True))
    #
    #Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], domain=Interval(-d, 0, left_open=True))


if __name__ == '__main__':
    run()

# created on 2018-04-01
