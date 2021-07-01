from util import *


@apply
def apply(given):
    (function, (x,)), x0 = given.of(Equal[ArgMin])
    fx0 = function._subs(x, x0)
    return LessEqual(fx0, function)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    Eq << apply(Equal(x0, ArgMin[x](f(x))))

    Eq << algebra.eq.imply.eq.argmin.definition.apply(Eq[0])

    Eq << algebra.eq_minimize.imply.all_le.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
