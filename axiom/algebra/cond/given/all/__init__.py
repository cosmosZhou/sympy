from util import *


@apply
def apply(given, var=None):
    if var is None:
        var = given.wrt
    from axiom.algebra.cond.imply.all import all
    return all(given, var)


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol(positive=True)
    f = Function(shape=(), integer=True)
    Eq << apply(f(e) > 0)

    Eq << algebra.all.imply.ou.apply(Eq[1])

    Eq << Eq[-1].subs(Eq[1].variable, e)


if __name__ == '__main__':
    run()

from . import domain_defined
# created on 2019-03-15
