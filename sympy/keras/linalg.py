from sympy.core.function import Function
from sympy.concrete.expr_with_limits import Lamda
from sympy.functions.special.tensor_functions import Bool
from sympy.sets.contains import Contains
from sympy import Range


# https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part
def BandPart(x, *limits):
    (num_lower,), (num_upper,) = limits
    m, n = x.shape
    excludes = num_lower.free_symbols | num_upper.free_symbols
    i = x.generate_var(excludes=excludes, var='i', integer=True)
    excludes.add(i)
    j = x.generate_var(excludes=excludes, var='j', integer=True)
    
    return x * Lamda[j:n, i:m](Bool(Contains(i - j, Range(-num_upper, num_lower + 1))))

   
BandPart = Function.BandPart(eval=BandPart, complex=True)
band_part = BandPart
