from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    from axiom.algebra.all.imply.et.split import split_all
    et = split_all(given, cond, wrt)
    return et.args


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    f = Function(integer=True, shape=())
    d = Symbol(real=True, positive=True)
    Eq << apply(All[x:-d:d](f(x) > 0), cond=x <= 0)

    Eq << algebra.all.imply.et.split.apply(Eq[0], cond=x <= 0)




if __name__ == '__main__':
    run()

# created on 2018-12-16
