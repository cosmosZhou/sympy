from sympy import *


def initial_offset(r, w, i=0):
    return (w.shape[i] - 1) // 2 * r[i] + (r[i] // 2) * (1 - w.shape[i] % 2)


def limit(r, w, n0, di, i0, index=0):
    return slice(di, Max(0, -(i0 // r[index])), Min(-1 // r[index] + w.shape[index], (n0 - i0 - 1) // r[index]) + 1)


def shape(self):
    x, w, *limits = self.args
    return x.shape[:-1] + w.shape[-1:]


def conv1d(x, w, *limits):
    if limits:
        (r,), *_ = limits
    else:
        r = 1
        
    _, in_channels, out_channels = w.shape
    * batch_size, n0, _in_channels = x.shape
    
    assert in_channels == _in_channels
    
    def conv1d(x, w): 
        i = Symbol.i(integer=True)
        di = Symbol.d_i(integer=True)
        
        d0 = initial_offset((r,), w)
        
        i0 = i - d0
        
        return LAMBDA[i:n0](Sum[limit((r,), w, n0, di, i0)](x[i0 + di * r] @ w[di]))
            
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
        r = (1, 1)
        
    l0, l1, in_channels, out_channels = w.shape
    * batch_size, n0, n1, _in_channels = x.shape
    
    assert in_channels == _in_channels        
    
    def conv2d(x, w):
        i = Symbol.i(integer=True)
        di = Symbol.d_i(integer=True)
        
        j = Symbol.j(integer=True)
        dj = Symbol.d_j(integer=True)
        
        d0 = initial_offset(r, w, 0)
        d1 = initial_offset(r, w, 1)
        
        i0 = i - d0
        j0 = j - d1
        
        return LAMBDA[j:n1, i:n0](Sum[limit(r, w, n1, dj, j0, 1), limit(r, w, n0, di, i0, 0)](x[i0 + di * r[0], j0 + dj * r[1]] @ w[di, dj]))
            
    if batch_size:
        batch_size = batch_size[0]
        k = Symbol.k(integer=True)        
        return LAMBDA[k:batch_size](conv2d(x[k], w))
    else:
        return conv2d(x, w)    


conv2d = Function.conv2d(real=True, nargs=(2,), eval=conv2d, shape=property(shape))


def conv3d(x, w, *limits):
    if limits:
        (r,), *_ = limits
    else:
        r = (1, 1, 1)
        
    l0, l1, l2, in_channels, out_channels = w.shape
    * batch_size, n0, n1, n2, _in_channels = x.shape
    
    assert in_channels == _in_channels        
    
    def conv3d(x, w):
        i = Symbol.i(integer=True)
        di = Symbol.d_i(integer=True)
        
        j = Symbol.j(integer=True)
        dj = Symbol.d_j(integer=True)
        
        t = Symbol.t(integer=True)
        dt = Symbol.d_t(integer=True)
        
        d0 = initial_offset(r, w, 0)
        d1 = initial_offset(r, w, 1)
        d2 = initial_offset(r, w, 2)
        
        i0 = i - d0
        j0 = j - d1
        t0 = t - d2
        
        return LAMBDA[t:n2, j:n1, i:n0](Sum[limit(r, w, n2, dt, t0, 2), limit(r, w, n1, dj, j0, 1), limit(r, w, n0, di, i0, 0)](x[i0 + di * r[0], j0 + dj * r[1], t0 + dt * r[2]] @ w[di, dj, dt]))
            
    if batch_size:
        batch_size = batch_size[0]
        k = Symbol.k(integer=True)        
        return LAMBDA[k:batch_size](conv3d(x[k], w))
    else:
        return conv3d(x, w)    


conv3d = Function.conv3d(real=True, nargs=(2,), eval=conv3d, shape=property(shape))

