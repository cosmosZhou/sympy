from util import *
import axiom



@apply
def apply(given):
    fn, fn1 = given.of(Necessary)        
    return Suffice(fn1, fn)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Necessary(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))
    
    Eq << Eq[0].reversed

        
if __name__ == '__main__':
    run()
