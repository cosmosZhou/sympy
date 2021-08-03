from util import *


@apply
def apply(et, axiom, *args, ret=0, **kwargs):
    eqs = et.of(And)
    f_eq = axiom.apply(*eqs, *args, **kwargs)
    assert f_eq.given == eqs
    
    if ret is not None:        
        eqs = eqs[ret]
        
    if isinstance(eqs, tuple):
        eqs = And(*eqs)
    return eqs, f_eq


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    axiom = algebra.ne.cond.imply.cond.subs
    Eq << apply(Unequal(x, y) & Unequal(g(KroneckerDelta(x, y)), f(x, y)), axiom, swap=True)

    Eq << Eq[0].this.apply(algebra.ne.cond.imply.cond.subs, swap=True)

    Eq << algebra.et.imply.et.apply(Eq[0])


if __name__ == '__main__':
    run()