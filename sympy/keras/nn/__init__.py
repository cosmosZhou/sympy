# def softmax(x):
#     return exp(x) / Sum(exp(x))
# 
#  
# softmax = Function.softmax(eval=softmax, is_positive=True)
from sympy.core.function import Function
from sympy.functions.elementary.miscellaneous import Max
from sympy.concrete.reduced import ReducedSum
from sympy.functions.elementary.exponential import exp


class Softmax(Function):
    r"""
    x is a vector
    softmax(x) = exp(x) / Sum(exp(x))
    Sum(softmax(x)) = 1
    """
    is_nonnegative = True
     
    def _eval_is_extended_positive(self):
        return self.arg.is_finite
        
    def _eval_is_zero(self):
        if self.arg.is_finite:
            return False            
    
    @classmethod
    def eval(cls, arg):
        ...
 
    def simplify(self, **_):
        return self
 
    def __getitem__(self, indices):
        if len(self.shape) == 1:
            x = self.arg
            return exp(x[indices]) / ReducedSum(exp(x))
        if isinstance(indices, tuple):
            i, *indices = indices
            return self.func(self.arg[i])[indices]
        else:
            return self.func(self.arg[indices])
 
    def __iter__(self):
        raise TypeError
 
    def _latex(self, p):
        return r"softmax\left(%s\right)" % p._print(self.arg)
 
     
softmax = Softmax


# https://tensorflow.google.cn/api_docs/python/tf/nn/relu?hl=en
def relu(x):
    '''
    >>> x = Symbol(real=True) 
    >>> relu(x).this.defun()
    '''
    return Max(x, 0)


relu = Function.relu(real=True,
                     extended_negative=False,
                     eval=relu,
                     _eval_is_extended_integer=lambda self: self.arg.is_extended_integer,
                     _eval_is_extended_positive=lambda self: self.arg.is_extended_positive,
                     __doc__=relu.__doc__
                     )


def sigmoid(x):
    return Max(x, 0)


sigmoid = Function.σ(real=True,
                     extended_negative=False,
                     eval=sigmoid)
