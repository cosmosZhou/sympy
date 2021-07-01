from util import *


@apply(given=None)
def apply(given, epsilon=None, delta=None):
    return Equivalent(given, any_all(given, epsilon, delta))


def any_all(given, epsilon=None, delta=None):
    (fx, (x, x0, direction)), a = given.of(Equal[Limit])
    
    if epsilon is None:
        epsilon = given.generate_var(real=True, positive=True, var='epsilon')
    else:
        assert epsilon > 0
        
    if fx.is_real:
        assert a.is_real
    else:
        assert fx.is_complex
        assert a.is_complex
        
    kwargs = {}
    if x.is_integer: 
        kwargs['integer'] = True
        kwargs['var'] = 'N' if delta is None else delta
    else:
        kwargs['real'] = True
        kwargs['var'] = 'delta' if delta is None else delta
    
    if delta is None:
        delta = given.generate_var(positive=True, **kwargs)
    else:
        assert delta > 0
        
    assert not x.is_integer or x.is_integer and x0.is_infinite
# https://en.wikipedia.org/wiki/Limit_of_a_function        
    if x0.is_Infinity:
# https://en.wikipedia.org/wiki/Limit_of_a_function
# Limits at infinity   
        cond = x > delta
    elif x0.is_NegativeInfinity:
        cond = x < -delta
# "epsilon–delta definition of limit"
# https://en.wikipedia.org/wiki/(%CE%B5,_%CE%B4)-definition_of_limit        
    elif x.shape:
        cond = (0 < Norm(x - x0)) & (Norm(x - x0) < delta)
    elif not x.is_real or direction == 0:
        cond = (0 < abs(x - x0)) & (abs(x - x0) < delta)
    elif direction == 1:
        cond = (0 < x - x0) & (x - x0 < delta)
    elif direction == -1:
        cond = (0 < x0 - x) & (x0 - x < delta)
    else:
        ...
        
    if a.is_Infinity:
# https://en.wikipedia.org/wiki/One-sided_limit
        epsilon_constraint = fx > epsilon
    elif a.is_NegativeInfinity:
        epsilon_constraint = fx < -epsilon
    else:
        epsilon_constraint = abs(fx - a) < epsilon
        
    return Any[delta](All[x:cond](epsilon_constraint))


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
    #x0 = -oo
    a = Symbol.a(real=True)
    #a = oo
    #a = -oo
    direction = 1
    Eq << apply(Equal(Limit[x:x0:direction](f(x)), a))


if __name__ == '__main__':
    run()
# https://baike.baidu.com/item/戴德金定理
# https://baike.baidu.com/item/单调有界定理#3
# The monotone bounded convergence theorem
