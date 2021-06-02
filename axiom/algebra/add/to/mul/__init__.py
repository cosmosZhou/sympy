from util import *
import axiom



@apply
def apply(self):
    args = self.of(Add)
    common_terms = None
    for arg in args:
        if arg.is_Mul:
            if common_terms is None:
                common_terms = {*arg.args}
            else:
                common_terms &= {*arg.args}
        else:
            if common_terms is None:
                common_terms = {arg}
            else:
                common_terms &= {arg}
        if not common_terms:
            return
        
    additives = []
    for arg in args:
        if arg.is_Mul:
            arg = Mul(*{*arg.args} - common_terms)
            additives.append(arg)
        
    return Equal(self, Add(*additives) * Mul(*common_terms))


@prove
def prove(Eq):
    a = Symbol.a(complex=True)
    x = Symbol.x(complex=True)
    y = Symbol.y(complex=True)
    
    Eq << apply(a * x - a * y)
    
    Eq << Eq[0].this.rhs.expand()
    
    
if __name__ == '__main__':
    run()

from . import st

