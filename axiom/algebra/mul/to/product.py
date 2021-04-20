from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    function_limits_coeff = self._detect_multiple_products()
    assert function_limits_coeff is not None
    
    function, limits, coeff, last_product = function_limits_coeff
    if len(function) == 1:        
        coeff = self.func(*coeff)
        prod = last_product.try_absorb(coeff)
        if prod is None:            
            if last_product.limits == limits:
                function = function[0]
                prod = Product(last_product.function * function, *limits)
            else:
                return
            
    elif len(function) > 1:
        prod = Product(self.func(*function).simplify(), *limits)
        if coeff:
            prod *= self.func(*coeff)
    
    return Equal(self, prod)


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(Product[k:n](f(k)) * Product[k:n](g(k)))
    
    
if __name__ == '__main__':
    prove()
