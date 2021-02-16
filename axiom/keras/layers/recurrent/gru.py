from axiom.utility import prove, apply

from sympy import *
from axiom import algebre

from tensorflow.nn.recurrent.gru import GRU
from tensorflow.nn import sigmoid


@apply(imply=True)
def apply(x, Wx, Wh, b):
    h = Symbol.h(definition=GRU[Wx, Wh, b](x))
    t = Symbol.t(integer=True, positive=True)
    
    d = h[t - 1].shape[-1]
    Wxz = Symbol.W_xz(definition=Wx[:, :d])
    Wxr = Symbol.W_xr(definition=Wx[:, d:2 * d])
    Wxh = Symbol.W_xh(definition=Wx[:, -d:])
     
    Whz = Symbol.W_hz(definition=Wh[:, :d])
    Whr = Symbol.W_hr(definition=Wh[:, d:2 * d])
    Whh = Symbol.W_hh(definition=Wh[:, -d:])
     
    bz = Symbol.b_z(definition=b[:d])
    br = Symbol.b_r(definition=b[d:2 * d])
    bh = Symbol.b_h(definition=b[-d:])
  
    zt = Symbol.z_t(definition=sigmoid(x[t] @ Wxz + h[t - 1] @ Whz + bz)) 
    rt = Symbol.r_t(definition=sigmoid(x[t] @ Wxr + h[t - 1] @ Whr + br))     
    gh = Symbol(r"\tilde{h}_t", definition=tanh(x[t] @ Wxh + (rt * h[t - 1]) @ Whh + bh))
    
    return Equality(h[t], (1 - zt) * gh + zt * h[t - 1])


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    
    dx = Symbol.d_x(integer=True, positive=True)
    dh = Symbol.d_h(integer=True, positive=True)
    
    x = Symbol.x(real=True, shape=(n, dx))
    Wx = Symbol("W^x", real=True, shape=(dx, 3 * dh))
    Wh = Symbol("W^h", real=True, shape=(dh, 3 * dh))
    b = Symbol.b(real=True, shape=(3 * dh,))
    
    Eq << apply(x, Wx, Wh, b)
    
    t = Eq[-1].lhs.index
    
    Eq << Eq[0].this.rhs.definition
         
    Eq <<= Eq[-1][t - 1], Eq[-1][t]
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].subs(Eq[-3].reversed)
    
    Eq << Eq[-1].subs(*(Eq[i].reversed for i in range(1, 13)))

if __name__ == '__main__':
    prove(__file__)
