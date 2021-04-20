from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete


def H_step(x):
    if not x.shape:
        return x 
    assert len(x.shape) == 1
    n = x.shape[0] 
    if n == 2:
        return x[1] * x[0] + 1
    return Piecewise((x[0], Equal(n, 1)),
                     (x[1] * x[0] + 1, Equal(n, 2)),
                     (H(x[:n - 1]) * x[n - 1] + H(x[:n - 2]), True))


def K_step(x):
    if not x.shape:
        return S.One
    assert len(x.shape) == 1
    n = x.shape[0]
    if n == 2:
        return x[1]
    return Piecewise((1, Equal(n, 1)),
                     (x[1], Equal(n, 2)),
                     (K(x[:n - 1]) * x[n - 1] + K(x[:n - 2]), True))


H = Function.H(integer=True, eval=H_step, shape=())

K = Function.K(integer=True, eval=K_step, shape=())    


def HK(x):
    n = x.generate_free_symbol(integer=True, free_symbol='n')
    return Symbol.H(LAMBDA[n](H(x[:n + 1]))), Symbol.K(LAMBDA[n](K(x[:n + 1])))


@apply
def apply(x, n, H=None, K=None):    
    assert n > 0    
    if H is None or K is None:
        H, K = HK(x)
        
    return Equal(H[n + 1], H[n - 1] + H[n] * x[n + 1]), \
        Equal(K[n + 1], K[n - 1] + K[n] * x[n + 1]) 


@prove
def prove(Eq): 
    x = Symbol.x(integer=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    
    Eq << apply(x, n)
    
    H = Eq[0].lhs.base
    K = Eq[1].lhs.base
    Eq <<= H[n + 1].this.definition.this.rhs.definition, K[n + 1].this.definition.this.rhs.definition
    
    Eq <<= Eq[-2].this.rhs.subs(H[n].this.definition.reversed, H[n - 1].this.definition.reversed), \
    Eq[-1].this.rhs.subs(K[n].this.definition.reversed, K[n - 1].this.definition.reversed)

if __name__ == '__main__':
    prove()
