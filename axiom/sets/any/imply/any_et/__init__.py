from util import *


@apply
def apply(given):
    function, *limits = given.of(Any)
    return Any[given.variables](And(function, given.limits_cond).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    f = Function.f(shape=(), integer=True)

    Eq << apply(Any[x:A, y:B](f(x, y) > 0))

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()


from . import single_variable
