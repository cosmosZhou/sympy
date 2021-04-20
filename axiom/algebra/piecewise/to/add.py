from sympy import *
from axiom.utility import prove, apply
import axiom

@apply
def apply(piecewise, additive=None):
    ec = axiom.is_Piecewise(piecewise)
    ec = [(e + additive, c)for e, c in ec]
     
    return Equal(piecewise, Add(piecewise.func(*ec), -additive))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,))
    y = Symbol.y(real=True, shape=(k,))
    z = Symbol.z(real=True, shape=())
    A = Symbol.A(etype=dtype.real * k)
    g = Function.g(shape=(), real=True)
    f = Function.f(shape=(), real=True)
    h = Function.h(shape=(), real=True)
     
    Eq << apply(Piecewise((g(x), Equal(x, y)), (f(x), Contains(y, A)), (h(x), True)), z)
    
    Eq << Eq[-1].this.rhs.args[1].astype(Add)
    
if __name__ == '__main__':
    prove()