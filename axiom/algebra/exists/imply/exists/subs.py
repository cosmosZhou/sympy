from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from sympy.concrete.limits import limits_sort


@apply
def apply(self, old, new):
    function, *limits = axiom.is_Exists(self)
    assert not new.is_given
    assert not self.function._has(new)
    
    limits_dict = self.limits_dict
    assert new not in limits_dict
       
    keys = old.free_symbols & limits_dict.keys()
    
    assert keys
    
    function = function._subs(old, new)
    assert not function.has(*keys)
    
    for key in keys:
        assert limits_dict[key] == []
        del limits_dict[key]
        
    limits_dict[new] = []
    
    limits = limits_sort(limits_dict)
    
    return Exists(function, *limits)


@prove
def prove(Eq): 
    e = Symbol.e(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    A = Function.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real, given=True)
    
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Exists[e, a:A(b), b:B](f(e) * a > g(f(e)) * b), f(e), x)
    
    Eq << algebra.exists.given.exists.subs.apply(Eq[1], x, f(e))
    
    Eq << ~Eq[-1]
    
    Eq << algebra.forall.exists.imply.exists_et.apply(Eq[-1], Eq[0])    

if __name__ == '__main__':
    prove()

