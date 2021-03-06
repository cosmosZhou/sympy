from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply(imply=True)
def apply(piecewise, evaluate=False):
    ec0, ec1, *ec = piecewise.args
    
    e0, c0 = ec0
    e1, c1 = ec1
    if not ec:
        return Equality(piecewise, Piecewise((e1, c0.invert()), (e0, True)), evaluate=evaluate) 
    
    return Equality(piecewise, Piecewise((e1, c1 & c0.invert()), (e0, c0), *ec), evaluate=evaluate)


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,))
    A = Symbol.A(etype=dtype.real * k)
    B = Symbol.B(etype=dtype.real * k)
    f = Function.f(nargs=(k,), shape=(), real=True)
    g = Function.g(nargs=(k,), shape=(), real=True)
    h = Function.h(nargs=(k,), shape=(), real=True)
     
    Eq << apply(Piecewise((f(x), Contains(x, A)), (g(x), Contains(x, B)), (h(x), True)))
    
    p = Symbol.p(definition=Eq[0].lhs)
    q = Symbol.q(definition=Eq[0].rhs)
    Eq << p.this.definition
    
    Eq << q.this.definition
        
    Eq << algebre.equal.imply.ou.general.apply(Eq[-1])
    
    Eq << algebre.ou.imply.equal.general.apply(Eq[-1], wrt=q)
    
    Eq << Eq[-1].subs(Eq[1].reversed).reversed
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove(__file__)

