from util import *
import axiom



@apply
def apply(imply):
    function, *limits = imply.of(Exists)
    assert all(len(limit) == 1 for limit in limits)
    return function


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(Exists[e](f(e) > 0))

    Eq << algebra.cond.imply.any.apply(Eq[1], wrt=e)


if __name__ == '__main__':
    run()

