from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from sympy.logic.boolalg import Boolean
from axiom.algebra.sum.to.add.dissect import dissect


def split_forall(given, cond, wrt):
    assert given.is_ForAll
    
    if isinstance(cond, Boolean):
        if wrt is None:
            wrt = cond.wrt
        
        cond = wrt.domain_conditioned(cond)
    
        if wrt not in given.variables:
            domain = given.domain_defined(wrt)
            given = ForAll(given.function, *given.limits, (wrt, domain))
    
    return dissect(given, cond, wrt=wrt)

    
@apply
def apply(given, *, cond=None, wrt=None):
    return split_forall(given, cond, wrt)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(integer=True, shape=())
    d = Symbol.d(real=True, positive=True)
# for x > 0
#     Eq << apply(ForAll[x:-d:d](f(x) > 0), cond=x > 0)
#     
#     Eq << algebra.et.given.cond.apply(Eq[-1])
#     
#     Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(0, d, left_open=True))
#     
#     Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(-d, 0))

# for x >= 0
#     Eq << apply(ForAll[x:-d:d](f(x) > 0), cond=x >= 0)
#     
#     Eq << algebra.et.given.cond.apply(Eq[-1])
#     
#     Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(0, d))
#     
#     Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(-d, 0, right_open=True))
    
# for x < 0
#     Eq << apply(ForAll[x:-d:d](f(x) > 0), cond=x < 0)
#     
#     Eq << algebra.et.given.cond.apply(Eq[-1])
#     
#     Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(0, d))
#     
#     Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(-d, 0, right_open=True))
    
# for x:(-d,d), x < 0    
    Eq << apply(ForAll[x:Interval(-d, d, left_open=True, right_open=True)](f(x) > 0), cond=x < 0)
     
    Eq << algebra.et.given.cond.apply(Eq[-1])
     
    Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(0, d, right_open=True))
     
    Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(-d, 0, right_open=True, left_open=True))

# for x <= 0
#     Eq << apply(ForAll[x:-d:d](f(x) > 0), cond=x <= 0)
#      
#     Eq << algebra.et.given.cond.apply(Eq[-1])
#      
#     Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(0, d, left_open=True))
#      
#     Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(-d, 0))

# for x in (-d, d) cond = x <= 0    
#     Eq << apply(ForAll[x:Interval(-d, d, left_open=True, right_open=True)](f(x) > 0), cond=x <= 0)
#      
#     Eq << algebra.et.given.cond.apply(Eq[-1])
#      
#     Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(0, d, left_open=True, right_open=True))
#      
#     Eq << algebra.forall.imply.forall.limits.restrict.apply(Eq[0], domain=Interval(-d, 0, left_open=True))
    
    
if __name__ == '__main__':
    prove()

