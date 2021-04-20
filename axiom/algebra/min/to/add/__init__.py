from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra

def rewrite_from_MinMaxBase(self):
    common_terms = None
    
    for plus in self.args:
        if isinstance(plus, Add):
            if common_terms is None:
                common_terms = {*plus.args}
            else:
                common_terms &= {*plus.args}
        else:
            if common_terms is None:
                common_terms = {plus}
            else:
                common_terms &= {plus}
    if common_terms:
        args = []
        for e in self.args:
            if isinstance(e, Add):
                e = Add(*{*e.args} - common_terms)
            elif e.is_Zero:
                ...
            else:
                e = 0
            args.append(e)
        return Add(*common_terms, self.func(*args))    

@apply
def apply(self): 
    axiom.is_Min(self)
    
    return Equal(self, rewrite_from_MinMaxBase(self))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    r = Symbol.r(real=True, positive=True)
    
    Eq << apply(Min(x * r + 1, y * r + 1))
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.astype(Add)
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    
    
if __name__ == '__main__':
    prove()
from . import relu
