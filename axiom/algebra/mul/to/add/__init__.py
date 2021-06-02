from util import *
import axiom



@apply
def apply(self): 
    for i, arg in enumerate(self.args):
        if isinstance(arg, Add): 
            summand = []
            for e in arg.args:
                args = [*self.args]
                args[i] = e 
                summand.append(self.func(*args))
            return Equal(self, Add(*summand))


@prove
def prove(Eq):
    x = Symbol.x(complex=True)
    a = Symbol.a(complex=True)
    b = Symbol.b(complex=True)
    Eq << apply(x * (a + b))
    
    Eq << Eq[-1].this.lhs.expand()
    
    
if __name__ == '__main__':
    run()

from . import st, square