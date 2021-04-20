
from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol
from axiom import keras

@apply
def apply(x, y, given):
    assert given.is_Equal
    W_T, W = given.args
    assert W_T == W.T
    
    return Equal(x @ W @ y, y @ W @ x)




@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    x = Symbol.x(shape=(n,), real=True)
    y = Symbol.y(shape=(n,), real=True)
    W = Symbol.W(shape=(n, n), real=True)
     
    Eq << apply(x, y, Equal(W.T, W))
    
    Eq << keras.nn.bilinear.transpose.apply(x, y, W)
    
    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    prove()
