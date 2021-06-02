from util import *
import axiom


@apply(given=None)
def apply(self):
    p, q = self.of(Suffice)        
    return Equivalent(self, p.invert() | q, evaluate=False)


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(integer=True)    
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    Eq << apply(Suffice(x > y, f(x) > g(y)))
        
if __name__ == '__main__':
    run()
