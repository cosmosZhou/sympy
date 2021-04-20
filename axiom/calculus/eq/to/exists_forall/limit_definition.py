from sympy import *
from axiom.utility import prove, apply
import axiom


def exists_forall(given, ε=None, δ=None):
    limit_expr, a = axiom.is_Equal(given)
    
    
    if ε is None:
        ε = limit_expr.generate_free_symbol(real=True, positive=True, free_symbol='ε')
    else:
        assert ε > 0
        
    fx, (x, x0, direction) = limit_expr.args
    
    if fx.is_real:
        assert a.is_real
    else:
        assert fx.is_complex
        assert a.is_complex
        
    kwargs = {}
    if x.is_integer:        
        kwargs['integer'] = True
        kwargs['free_symbol'] = 'N' if δ is None else δ
    else:
        kwargs['real'] = True
        kwargs['free_symbol'] = 'δ' if δ is None else δ
    
    if δ is None:
        δ = limit_expr.generate_free_symbol(positive=True, **kwargs)
    else:
        assert δ > 0
        
    assert not x.is_integer or x.is_integer and x0.is_infinite
# https://en.wikipedia.org/wiki/Limit_of_a_function        
    if x0.is_Infinity:
# https://en.wikipedia.org/wiki/Limit_of_a_function
# Limits at infinity   
        cond = x > δ
    elif x0.is_NegativeInfinity:
        cond = x < -δ
# "epsilon–delta definition of limit"
# https://en.wikipedia.org/wiki/(%CE%B5,_%CE%B4)-definition_of_limit        
    elif x.shape:
        cond = (0 < Norm(x - x0)) & (Norm(x - x0) < δ)
    elif not x.is_real or direction == 0:
        cond = (0 < abs(x - x0)) & (abs(x - x0) < δ)
    elif direction == 1:
        cond = (0 < x - x0) & (x - x0 < δ)
    elif direction == -1:
        cond = (0 < x0 - x) & (x0 - x < δ)
    else:
        ...
        
    if a.is_Infinity:
# https://en.wikipedia.org/wiki/One-sided_limit
        epsilon_constraint = fx > ε
    elif a.is_NegativeInfinity:
        epsilon_constraint = fx < -ε
    else:
        epsilon_constraint = abs(fx - a) < ε
        
    return Exists[δ](ForAll[x:cond](epsilon_constraint))

    
@apply(given=None)
def apply(given, ε=None, δ=None):
    return Equivalent(given, exists_forall(given, ε, δ))


@prove(provable=False)
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    
    x = Symbol.x(real=True)
    x = Symbol.x(real=True, shape=(n,))
    x = Symbol.x(integer=True)
    
    f = Function.f(real=True, shape=())
        
    x0 = Symbol.x0(real=True)
    x0 = Symbol.x0(real=True, shape=(n,))
    
    x0 = oo
#     x0 = -oo
    
    a = Symbol.a(real=True)    
#     a = oo
#     a = -oo

    direction = 1
    
    Eq << apply(Equal(Limit[x:x0:direction](f(x)), a))


if __name__ == '__main__':
    prove()
# https://baike.baidu.com/item/戴德金定理
# https://baike.baidu.com/item/单调有界定理#3
# The monotone bounded convergence theorem
