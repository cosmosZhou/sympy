from sympy import *


# https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part
def BandPart(x, *limits):
    (num_lower,), (num_upper,) = limits
    m, n = x.shape
    excludes = num_lower.free_symbols | num_upper.free_symbols
    i = x.generate_free_symbol(excludes=excludes, free_symbol='i', integer=True)
    excludes.add(i)
    j = x.generate_free_symbol(excludes=excludes, free_symbol='j', integer=True)
    
    return x * LAMBDA[j:n, i:m](Boole(Contains(i - j, Interval(-num_upper, num_lower, integer=True))))

   
BandPart = Function.BandPart(eval=BandPart, complex=True)
band_part = BandPart
