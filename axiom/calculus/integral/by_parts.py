from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, calculus


@apply
def apply(integral, u=None, dv=None):
    if len(integral.limits) != 1:
        return
    
    (x, a, b), *_ = integral.limits
    if u is not None:
        dv = integral.function / u
        v = integral.func(dv, x).doit()
        du = diff(u, x)
    elif dv is not None:
        u = integral.function / dv
        v = integral.func(dv, x).doit()
        du = diff(u, x)
    else:
        ...
# u * dv = d(u v) - du * v
    f = (u * v)._eval_interval(x, a, b) - integral.func(du * v, *integral.limits).simplify()
    return Equal(integral, f)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    u = Function.u(shape=(), real=True)
    v = Function.v(shape=(), real=True)    
    
    Eq << apply(Integral(u(x) * diff(v(x), x), (x, a, b)), u=u(x))
    
    uv = Function.uv(shape=(), real=True, eval=lambda x : u(x) * v(x))
    
    Eq << diff(uv(x), x).this.expr.definition
    
    Eq << Eq[-1].this.rhs.doit()
    
    Eq << Eq[0] - Eq[0].rhs.args[-1]
    
    Eq << Eq[-1].this.lhs.apply(calculus.add.to.integral)
    
    Eq << Eq[-1].subs(Eq[-3].reversed)
    
    Eq << Eq[-1].this.lhs.doit()
    
    Eq << Eq[-1].this.lhs.args[-1].definition
    
    Eq << Eq[-1].this.lhs.definition

    
if __name__ == '__main__':
    prove()

