from util import *


@apply
def apply(given):
    fn, fn1 = given.of(Equivalent)        
    return Suffice(fn, fn1), Necessary(fn, fn1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Equivalent(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))
    
    Eq <<= Eq[-1] & Eq[-2]

        
if __name__ == '__main__':
    run()
