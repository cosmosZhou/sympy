from util import *


@apply
def apply(cond, ou):
    if not ou.is_Or:
        cond, ou = ou, cond
    args = ou.of(Or)
    
    return Or(*((arg & cond).simplify() for arg in args))


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    c = Symbol.c(integer=True, given=True)
    d = Symbol.d(integer=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply(f(x) < g(y), (a < b) | (c < d))

    Eq << algebra.ou.imply.et.collect.apply(Eq[-1], cond=f(x) < g(y))


if __name__ == '__main__':
    run()