from util import *


@apply
def apply(cond, exists):
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
    Eq << apply(f(y) > 0, Any[x:A](g(x) > 0))

    Eq << algebra.any_et.imply.et.any.apply(Eq[-1])


if __name__ == '__main__':
    run()