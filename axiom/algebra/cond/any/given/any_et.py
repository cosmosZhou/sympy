from util import *


@apply
def apply(cond, any):
    fn, *limits = any.of(Any)

    assert not cond.has(*any.variables)
    return Any(fn & cond, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    f, g = Function(integer=True)
    Eq << apply(f(y) > 0, Any[x:A](g(x) > 0))

    Eq << algebra.any_et.imply.et.any.apply(Eq[-1])
    Eq << algebra.et.imply.et.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-08-24
