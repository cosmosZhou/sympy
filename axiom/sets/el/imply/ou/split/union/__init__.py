from util import *


def split(self, simplify=True):
    assert self.is_Element
    e, domain = self.args
    
    eqs = [Element(e, s) for s in domain.of(Union)]
        
    if simplify:
        eqs = [eq.simplify() for eq in eqs]
        
    return Or(*eqs)
    
    
@apply(simplify=False)
def apply(self, simplify=True):
    return split(self, simplify=simplify)


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    A, B, C = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A | B | C))

    Eq << Eq[1].simplify()


if __name__ == '__main__':
    run()

from . import two
