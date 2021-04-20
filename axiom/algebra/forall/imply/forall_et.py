from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from sympy.concrete.limits import limits_cond


@apply
def apply(given, index=None):
    fn, *limits = axiom.is_ForAll(given)
    
    if index is None:
        cond = limits_cond(limits)
    else:
        if isinstance(index, slice):
            cond = limits_cond(limits[index])
        else:
            cond = limits_cond([limits[index]])
    return ForAll(fn & cond, *limits)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    
    Eq << apply(ForAll[x:g(x) > 0](f(x) > 0))
    
    Eq << algebra.forall_et.given.forall.apply(Eq[-1])

    
if __name__ == '__main__':
    prove()

