from sympy.core.function import Function
from sympy.concrete.expr_with_limits import Lamda
from sympy.functions.special.tensor_functions import Bool
from sympy.sets.contains import Element
from sympy import Range


# https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part
def BandPart(x, *limits):
    '''
    >>> m, n, l, u = Symbol(integer=True, positive=True)
    >>> x = Symbol(real=True, shape=(m, n))
    >>> BandPart[l, u](x).this.defun()
    '''
    
    (num_lower,), (num_upper,) = limits
    m, n = x.shape
    excludes = num_lower.free_symbols | num_upper.free_symbols
    i = x.generate_var(excludes=excludes, var='i', integer=True)
    excludes.add(i)
    j = x.generate_var(excludes=excludes, var='j', integer=True)
    
    return x * Lamda[j:n, i:m](Bool(Element(i - j, Range(-num_upper, num_lower + 1))))

   
BandPart = Function.BandPart(eval=BandPart, complex=True, __doc__=BandPart.__doc__)
band_part = BandPart
