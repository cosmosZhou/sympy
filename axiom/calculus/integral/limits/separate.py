from util import *


@apply
def apply(sgm):
    function, *limits = sgm.of(Integral)
    assert len(limits) > 1
    limit, *limits = limits

    function = sgm.func(function, limit).simplify()

    return Equal(sgm, sgm.func(function, *limits))


@prove
def prove(Eq):
    from axiom import calculus

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    d = Symbol.d(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply(Integral[x:a:b, y:c:d](f(y) * g(x, y)))

    Eq << Eq[-1].this.rhs.function.apply(calculus.mul.to.integral)


if __name__ == '__main__':
    run()