from sympy import *

from tensorflow.nn import sigmoid

def lstm_recursive(x, *limits):
    (W,), (Wh,), (b,), (t,) = limits 
    hc = lstm[W, Wh, b, t - 1](x)
    
    xt = x[t]
    h = Indexed(hc, 0)
    c = Indexed(hc, 1)    
    d = h.shape[-1]
    
    Wi = W[:,:d]
    Wf = W[:, d:2 * d]
    Wc = W[:, 2 * d:3 * d]
    Wo = W[:, -d:]

    Whi = Wh[:,:d]
    Whf = Wh[:, d:2 * d]
    Whc = Wh[:, 2 * d:3 * d]
    Who = Wh[:, -d:]    
    
    bi = b[:d]
    bf = b[d:2 * d]
    bc = b[2 * d:3 * d]
    bo = b[-d:]

    i = sigmoid(xt @ Wi + h @ Whi + bi)
    f = sigmoid(xt @ Wf + h @ Whf + bf)
    c = f * c + i * tanh(xt @ Wc + h @ Whc + bc)
    o = sigmoid(xt @ Wo + h @ Who + bo)    
     
    return Piecewise((BlockMatrix(o * tanh(c), c), t > 0), (ZeroMatrix(*hc.shape), True))


def shape(self):
    (Wh,) = self.limits[1]
    d = Wh.shape[-1] / 4
    if len(self.limits) > 3:
        return (2, d)
    
    x = self.arg
    x_shape = x.shape
    shape = (x_shape[-2], d)
    if len(x_shape) > 2:
        shape = (x[0],) + shape
    return shape


lstm = Function.lstm(real=True, integer=None, eval=lstm_recursive, shape=property(shape))

    
def LSTM(x, *weights):
    (W,), (Wh,), (b,) = weights
    n = x.shape[0]
    t = Symbol.t(integer=True)
    return LAMBDA[t:n](Indexed(lstm[W, Wh, b, t](x), 0))


def LSTMCell(x, *weights):
    (W,), (Wh,), (b,) = weights
    n = x.shape[0]
    t = Symbol.t(integer=True)
    return LAMBDA[t:n](Indexed(lstm[W, Wh, b, t](x), 1))


LSTM = Function.LSTM(real=True, integer=None, eval=LSTM, shape=property(shape))

LSTMCell = Function.LSTMCell(real=True, integer=None, eval=LSTMCell, shape=property(shape))

