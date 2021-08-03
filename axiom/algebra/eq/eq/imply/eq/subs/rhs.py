from util import *


@apply
def apply(eq, f_eq, swap=False, reverse=False, simplify=True, assumptions={}):
    from axiom.algebra.all_eq.cond.imply.all.subs import subs
    if swap:
        f_eq, eq = eq, f_eq
        
    old, new = eq.of(Equal)
    lhs, rhs = f_eq.of(Equal)
    
    if reverse:
        old, new = new, old
    
    return Equal(lhs, subs(rhs, old, new, simplify=simplify, assumptions=assumptions))


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True, shape=(m, n))
    b = Symbol.b(real=True, shape=(m, n))
    c = Symbol.c(real=True, shape=(m, n))
    d = Symbol.d(real=True, shape=(m, n))
    Eq << apply(Equal(a, 2 * c), Equal(a * b, d * a))

    Eq << Eq[1].subs(Eq[0])

    Eq << Eq[2].subs(Eq[0])


if __name__ == '__main__':
    run()