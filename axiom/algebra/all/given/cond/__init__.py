from util import *



@apply
def apply(given):
    fn, *limits = given.of(All)
    return fn


@prove
def prove(Eq):
    from axiom import algebra
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(All[e:S](f(e) > 0))

    Eq << algebra.all.given.ou.apply(Eq[0])

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=1)


if __name__ == '__main__':
    run()

from . import subs
