from util import *


@apply
def apply(given):
    x0, argmax_fx = given.of(Equal)
    function, [x] = argmax_fx.of(ArgMax)
    fx0 = function._subs(x, x0)
    return GreaterEqual(fx0, function)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    Eq << apply(Equal(x0, ArgMax[x](f(x))))

    Eq << algebra.eq.imply.eq.argmax.definition.apply(Eq[0])

    Eq << algebra.eq_maximize.imply.all_ge.apply(Eq[-1])


if __name__ == '__main__':
    run()
