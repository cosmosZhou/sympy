from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(piecewise, var):
    (expr, cond), (expr_else, _) = axiom.is_Piecewise(piecewise)
    eqs = axiom.is_And(cond)
    
    var_eqs = []
    non_var_eqs = []
    
    for eq in eqs:
        if eq._has(var):
            var_eqs.append(eq)
        else:
            non_var_eqs.append(eq)
            
    var_eqs = And(*var_eqs)
    non_var_eqs = And(*non_var_eqs)
    
    return Equal(piecewise, Piecewise((Piecewise((expr, non_var_eqs), (expr_else, True)), var_eqs), (expr_else, True)))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,))
    y = Symbol.y(real=True, shape=(k,))
    
    A = Symbol.A(etype=dtype.real * k)
    B = Symbol.B(etype=dtype.real * k)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    h = Function.h(shape=(), real=True)
     
    Eq << apply(Piecewise((f(x) * g(y), Contains(x, A) & Contains(y, B)), (h(x, y), True)), var=y)
    
    Eq << Eq[0].this.rhs.apply(algebra.piecewise.flatten, index=0)


if __name__ == '__main__':
    prove()

