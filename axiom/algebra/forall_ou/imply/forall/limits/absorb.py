from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, index, wrt=None):
    ou, *limits = axiom.forall_ou(given)
    
    eqs = axiom.is_Or(ou, copy=True)
    
    cond = eqs.pop(index)
    if wrt is None:
        wrt = cond.wrt
    else:
        cond._has(wrt)
    
    cond = cond.invert()
    
    domain = cond.domain_conditioned(wrt)
    for i, (x, *ab) in enumerate(limits):
        if x == wrt:
            if len(ab) == 2:
                a, b = ab
                assert not b.is_set
                domain = Interval(a, b, right_open=x.is_integer, integer=x.is_integer)
                domain &= cond.domain_conditioned(wrt)
                limits[i] = (x, domain)
                return ForAll(Or(*eqs), *limits)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)    
    c = Symbol.c(real=True)
    
    f = Function.f(shape=(), real=True)
    
    Eq << apply(ForAll[x:a:b]((x <= c) | (f(x) >= 1)), index=1)
    
    Eq << algebra.forall.given.ou.apply(Eq[1])
    
    Eq << Eq[-1].this.find(NotContains).apply(sets.notcontains.given.ou.split.intersection, simplify=None)
    
    Eq << Eq[-1].this.find(NotContains).apply(sets.notcontains.given.le.real, simplify=None)
    
    Eq << algebra.forall.imply.ou.apply(Eq[0])
     
    
       

if __name__ == '__main__':
    prove()

