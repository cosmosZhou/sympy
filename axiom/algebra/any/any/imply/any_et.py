from util import *
import axiom


@apply
def apply(*given):
    from sympy.concrete.limits import limits_dependent
    any_x, any_y = given
    fx, *limits_x = any_x.of(Exists)
    fy, *limits_y = any_y.of(Exists)

    assert not limits_dependent(limits_x, limits_y)

    return Exists(fx & fy, *limits_x, *limits_y)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)

    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Exists[x:A](f(x, y) > 0), Exists[y:B](g(y, x) > 0))

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.function.apply(algebra.cond.any.imply.any_et)


if __name__ == '__main__':
    run()

