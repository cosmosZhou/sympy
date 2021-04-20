from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from sympy.concrete.limits import limits_dict


@apply
def apply(given, old, new):
    (function, *limits_f), *limits_e = axiom.exists_forall(given)
    limits_f_dict = limits_dict(limits_f)
    
    domain = limits_f_dict[old]
    if domain == []:
        ...
    else:         
        assert new in domain
    
    return Exists(ForAll(function._subs(old, new) & function, *limits_f), *limits_e)


@prove
def prove(Eq):
    C = Symbol.C(real=True)
    
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    
    x0 = Symbol.x0(domain=A)
    
    f = Function.f(integer=True)
    
    Eq << apply(Exists[C](ForAll[x:A](f(x, C) > 0)), x, x0)
    
    Eq << Eq[-1].this.function.apply(algebra.forall_et.given.et)
    
    Eq << Eq[0].this.function.apply(algebra.forall.imply.et.subs, x, x0)
    
    
if __name__ == '__main__':
    prove()
