from util import *


@apply
def apply(imply):
    cond, exists = imply.of(And)
    if not exists.is_Any:
        cond, exists = exists, cond
    fn, *limits = exists.of(Any)

    assert not cond.has(*exists.variables)
    return Any(fn & cond, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    A = Symbol.A(etype=dtype.integer)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply((f(y) > 0) & Any[x:A](g(x) > 0))

    Eq << algebra.any_et.imply.any.split.apply(Eq[-1])

    Eq << algebra.et.given.conds.apply(Eq[0])


if __name__ == '__main__':
    run()

