from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre

def rewrite_from_MinMaxBase(self):
    common_terms = None
    
    for plus in self.args:
        if isinstance(plus, Plus):
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
            if isinstance(e, Plus):
                e = Plus(*{*e.args} - common_terms)
            elif e.is_Zero:
                ...
            else:
                e = 0
            args.append(e)
        return Plus(*common_terms, self.func(*args))    

@apply
def apply(self): 
    axiom.is_Max(self)
    
    return Equal(self, rewrite_from_MinMaxBase(self))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    r = Symbol.r(real=True, positive=True)
    
    Eq << apply(Max(x * r + 1, y * r + 1))    
    
    
    
if __name__ == '__main__':
    prove(__file__)
