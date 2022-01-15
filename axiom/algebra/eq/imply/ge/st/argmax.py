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

    x, x0 = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(x0, ArgMax[x](f(x))))

    Eq << algebra.eq.imply.eq.argmax.definition.apply(Eq[0])

    Eq << algebra.eq_maxima.imply.all_ge.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-04-13
