from util import *


@apply
def apply(eq, cond, axiom, *args, swap=False, index=None, **kwargs):    
    if swap:
        eq, cond = cond, eq    
    f_eq = axiom.apply(eq, cond, *args, **kwargs)
    assert f_eq.given == (eq, cond)
    
    if index:
        eq = cond
        
    return eq, f_eq


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    axiom = algebra.ne.cond.imply.cond
    Eq << apply(Unequal(x, y), Unequal(g(KroneckerDelta(x, y)), f(x, y)), axiom)

    Eq << algebra.ne.cond.imply.cond.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()
