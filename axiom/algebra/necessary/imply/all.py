from util import *



@apply
def apply(given, wrt=None):
    fn1, fn = given.of(Necessary)
    if wrt is None:
        wrt = fn.wrt
    return All[wrt:fn](fn1)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Necessary(Equal(f[n + 1], g[n + 1]), Equal(f[n], g[n])), wrt=n)

    Eq << Eq[0].apply(algebra.necessary.imply.ou)

    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=1, wrt=n)


if __name__ == '__main__':
    run()
