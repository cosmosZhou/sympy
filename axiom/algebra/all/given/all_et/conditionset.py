from util import *


@apply(simplify=False)
def apply(imply):
    import axiom
    fn, *limits = imply.of(ForAll)
    x, cond, baseset = axiom.limit_is_baseset(limits)
    return ForAll(fn & cond, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    A = Symbol.A(etype=dtype.integer)

    Eq << apply(ForAll[x:g(x) > 0:A](f(x) > 0))

    Eq << algebra.all_et.imply.all.apply(Eq[1])


if __name__ == '__main__':
    run()

