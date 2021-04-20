from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra

def piece_together(Sum, self):
    function = []
    limits = None        
    for arg in self.args:
        if isinstance(arg, Sum):
            function.append(arg.function)
            if limits is None:
                limits = arg.limits
            else:
                if limits != arg.limits:
                    return self
            continue

        additive = arg.astype(Sum)
        if additive is None:
            return self
        else:
            if limits is None:
                limits = additive.limits

            function.append(additive.function)
    
    return Sum(self.func(*function), *limits)

@apply
def apply(self):
    assert self.is_Add
    
    return Equal(self, piece_together(Sum, self))


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(Sum[k:n](f(k)) + Sum[k:n](g(k)))
    
    Eq << Eq[0].this.rhs.apply(algebra.sum.to.add)
    
    
if __name__ == '__main__':
    prove()
del limits
from . import limits
