from util import *
import axiom



@apply(simplify=False)
def apply(self, index=0): 
    args = self.of(Mul, copy=True)
    factor = args.pop(index)
    
    for i, plus in enumerate(args):
        if plus.is_Add:
            plus = Add(*(arg * factor for arg in plus.args))
            args[i] = plus
            return Equal(self, Mul(*args))


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    d = Symbol.d(real=True)
    r = Symbol.r(real=True)
    Eq << apply(-r * (a - b - c) / d)   
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1].this.rhs.expand()
    
    
if __name__ == '__main__':
    run()
