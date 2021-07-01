from util import *




@apply
def apply(imply, wrt=None):
    cond = imply.domain_defined(wrt)
    return Or(imply, NotContains(wrt, cond))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True, given=True)

    x = Symbol.x(shape=(n,), real=True, given=True)

    Eq << apply(x[i] > 0, wrt=i)

    Eq << algebra.ou.imply.all.apply(Eq[1], pivot=0)


if __name__ == '__main__':
    run()

