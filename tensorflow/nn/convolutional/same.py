from sympy import *


def conv1d(x, w):
    gram_width, embed_size, _embed_size = w.shape
    * batch_size, seq_length, __embed_size = x.shape
    
    assert embed_size == _embed_size == __embed_size
    
    def conv1d(x, w):
        d0 = (gram_width - 1) // 2
        i = Symbol.i(integer=True)
        j = Symbol.j(integer=True)
        return LAMBDA[i:seq_length](Sum[j:Max(i, d0):Min(gram_width + i, seq_length + d0)](x[j - d0] @ w[j - i]))        
            
    if batch_size:
        batch_size = batch_size[0]
        k = Symbol.k(integer=True)        
        return LAMBDA[k:batch_size](conv1d(x[k], w))
    else:
        return conv1d(x, w)    


conv1d = Function.conv1d(real=True, nargs=(2,), eval=conv1d)

