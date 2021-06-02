from util import *
import axiom



def split(self, simplify=True):
    assert self.is_Contains
    e, domain = self.args
    
    eqs = [Contains(e, s) for s in domain.of(Union)]
        
    if simplify:
        eqs = [eq.simplify() for eq in eqs]
        
    return Or(*eqs)
    
    
@apply(simplify=False)
def apply(self, simplify=True):
    return split(self, simplify=simplify)


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    C = Symbol.C(etype=dtype.integer, given=True)
    
    Eq << apply(Contains(e, A | B | C))
    
    Eq << Eq[1].simplify()
    

if __name__ == '__main__':
    run()

from . import two
