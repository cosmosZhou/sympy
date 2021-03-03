from sympy import *

def shape(self):
    x, w, *limits = self.args
    return x.shape[:-1] + w.shape[-1:]

def conv1d(x, w, *limits):
    if limits:
        (r,), *_ = limits
    else:
        r = 1
        
    _, in_channels, out_channels = w.shape
    * batch_size, seq_length, _in_channels = x.shape
    
    assert in_channels == _in_channels
    
    def conv1d(x, w):
        d0 = (w.shape[0] - 1) // 2
        i = Symbol.i(integer=True)
        di = Symbol.d_i(integer=True)
        
        d0 = d0 * r + (r // 2) * (1 - w.shape[0] % 2)
        i0 = i - d0
        return LAMBDA[i:seq_length](Sum[di:Max(0, -(i0 // r)):Min(-1 // r + w.shape[0], (seq_length - i0 - 1) // r) + 1](x[i0 + di * r] @ w[di]))
        return LAMBDA[i:seq_length](Sum[di:Max(0, -(i0 // r)):(Min(w.shape[0] * r, seq_length - i0) - 1) // r + 1](x[i0 + di * r] @ w[di]))
            
    if batch_size:
        batch_size = batch_size[0]
        k = Symbol.k(integer=True)        
        return LAMBDA[k:batch_size](conv1d(x[k], w))
    else:
        return conv1d(x, w)    


conv1d = Function.conv1d(real=True, nargs=(2,), eval=conv1d, shape=property(shape))

def conv2d(x, w, *limits):
    if limits:
        (r,), *_ = limits
    else:
        r = 1
        
    _, embed_size, _embed_size = w.shape
    * batch_size, seq_length, __embed_size = x.shape
    
    assert embed_size == _embed_size == __embed_size
    
    def conv2d(x, w):
        d0 = (w.shape[0] - 1) // 2
        i = Symbol.i(integer=True)
        di = Symbol.d_i(integer=True)
        
        d0 = d0 * r + (r // 2) * (1 - w.shape[0] % 2)
        i0 = i - d0
        return LAMBDA[i:seq_length](Sum[di:Max(0, -(i0 // r)):Min(-1 // r + w.shape[0], (seq_length - i0 - 1) // r) + 1](x[i0 + di * r] @ w[di]))
        return LAMBDA[i:seq_length](Sum[di:Max(0, -(i0 // r)):(Min(w.shape[0] * r, seq_length - i0) - 1) // r + 1](x[i0 + di * r] @ w[di]))
            
    if batch_size:
        batch_size = batch_size[0]
        k = Symbol.k(integer=True)        
        return LAMBDA[k:batch_size](conv2d(x[k], w))
    else:
        return conv2d(x, w)    


conv2d = Function.conv2d(real=True, nargs=(2,), eval=conv2d, shape=property(shape))

