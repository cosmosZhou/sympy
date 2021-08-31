from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    from axiom.algebra.all.imply.et.split import split_all
    given = split_all(given, cond, wrt)
    if given.is_And:
        lhs, rhs = given.of(And)
        return lhs, rhs
    else:
        return given


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    d = Symbol(real=True, positive=True)
    f = Function(integer=True)
    Eq << apply(All[x:-d:d](f(x) > 0), cond=x > 0)

    Eq << algebra.all.all.imply.all.limits_union.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

from . import all
