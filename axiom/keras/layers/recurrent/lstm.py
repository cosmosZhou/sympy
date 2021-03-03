from axiom.utility import prove, apply

from sympy import *
from axiom import algebre

from tensorflow.nn.recurrent.lstm import LSTM, LSTMCell
from tensorflow.nn import sigmoid


@apply
def apply(x, W, Wh, b):
    h = Symbol.h(LSTM[W, Wh, b](x))
    c = Symbol.c(LSTMCell[W, Wh, b](x))
    t = Symbol.t(integer=True, positive=True)
    
    d = h.shape[-1]
    
    Wi = Symbol.W_i(W[:,:d])
    Wf = Symbol.W_f(W[:, d:2 * d])
    Wc = Symbol.W_c(W[:, 2 * d:3 * d])
    Wo = Symbol.W_o(W[:, -d:])

    Whi = Symbol.W_hi(Wh[:,:d])
    Whf = Symbol.W_hf(Wh[:, d:2 * d])
    Whc = Symbol.W_hc(Wh[:, 2 * d:3 * d])
    Who = Symbol.W_ho(Wh[:, -d:])    
    
    bi = Symbol.b_i(b[:d])
    bf = Symbol.b_f(b[d:2 * d])
    bc = Symbol.b_c(b[2 * d:3 * d])
    bo = Symbol.b_o(b[-d:])

    it = Symbol.i_t(sigmoid(x[t] @ Wi + h[t - 1] @ Whi + bi))
    ft = Symbol.f_t(sigmoid(x[t] @ Wf + h[t - 1] @ Whf + bf))
    ct = Symbol.c_t(ft * c[t - 1] + it * tanh(x[t] @ Wc + h[t - 1] @ Whc + bc))
    ot = Symbol.o_t(sigmoid(x[t] @ Wo + h[t - 1] @ Who + bo))    
     
    return Equality(h[t], ot * tanh(ct))


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    
    dx = Symbol.d_x(integer=True, positive=True)
    dh = Symbol.d_h(integer=True, positive=True)
    
    x = Symbol.x(real=True, shape=(n, dx))
    W = Symbol("W", real=True, shape=(dx, 4 * dh))
    Wh = Symbol("W^h", real=True, shape=(dh, 4 * dh))
    b = Symbol.b(real=True, shape=(4 * dh,))
    
    Eq << apply(x, W, Wh, b)
    
    t = Eq[-1].lhs.index
    
    Eq << Eq[0].this.rhs.definition
    
    Eq <<= Eq[-1][t - 1], Eq[-1][t]
    
    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-1].subs(Eq[-3].reversed)
    
    Eq << Eq[9].this.rhs.definition[t - 1]
    
    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(*(Eq[i].reversed for i in range(1, 9)))
    
    Eq << Eq[-1].subs(*(Eq[i].reversed for i in range(10, 18)))


if __name__ == '__main__':
    prove(__file__)