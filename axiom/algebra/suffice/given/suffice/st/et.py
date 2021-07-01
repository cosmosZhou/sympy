from util import *


@apply
def apply(given, index=-1):
    cond, et = given.of(Suffice)
    eqs = et.of(And)
    first = And(*eqs[:index])
    second = And(*eqs[index:])
    return Suffice(cond, first), Suffice(cond, second)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, nonnegative=True)
    x = Symbol.x(integer=True, nonnegative=True)
    y = Symbol.y(integer=True, nonnegative=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    h = Function.h(integer=True)
    Eq << apply(Suffice(x > y, (f(x) > g(y)) & (f(x) > h(y))))

    Eq << algebra.suffice.suffice.imply.suffice.et.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()
