from util import *


@apply
def apply(cond1, cond2, ou):
    if not ou.is_Or:
        if cond2.is_Or:
            cond2, ou = ou, cond2
        elif cond1.is_Or:
            cond1, ou = ou, cond1
        else:
            return
        
    args = ou.of(Or)
    
    cond = cond1 & cond2
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
    h = Function.h(real=True)
    g = Function.g(real=True)
    Eq << apply(f(x) < g(y), h(x) < g(y), (a < b) | (c < d))

    Eq << algebra.ou.imply.et.collect.apply(Eq[-1], cond=f(x) < g(y))
    Eq << algebra.et.imply.et.apply(Eq[-1])


if __name__ == '__main__':
    run()