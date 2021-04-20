from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from axiom.algebra.forall.imply.ou import rewrite_as_Or


@apply
def apply(given, old, new):
    assert new not in old.domain
    domain = old.domain_bounded
    assert domain is not None and new not in domain
    assert given._has(old)
    
    cond = given.forall((old,))
    old = old.unbounded
    assert old != new
    ou = rewrite_as_Or(cond)
    
    return ou._subs(old, new) 


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True, shape=(oo,))
    j = Symbol.j(integer=True)
    t = Symbol.t(domain=Interval(0, n, integer=True))
    
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(f(x, t) > g(t), t, y[j])
    
    Eq << Eq[0].forall((t,))
    
    t = Eq[-1].variable
    Eq << algebra.forall.imply.ou.subs.apply(Eq[-1], t, y[j])
    
if __name__ == '__main__':
    prove()

