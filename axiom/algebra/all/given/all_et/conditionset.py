from util import *


@apply(simplify=False)
def apply(imply):
    fn, (x, cond, baseset) = imply.of(All)
    return All[x:cond:baseset](fn & cond)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    A = Symbol.A(etype=dtype.integer)

    Eq << apply(All[x:g(x) > 0:A](f(x) > 0))

    Eq << algebra.all_et.imply.all.apply(Eq[1])


if __name__ == '__main__':
    run()

