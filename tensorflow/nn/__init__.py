from sympy import *

# def softmax(x):
#     return exp(x) / Sum(exp(x))
# 
#  
# softmax = Function.softmax(eval=softmax, is_positive=True)

  
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
            return self.definition[indices]
        if isinstance(indices, tuple):
            i, *indices = indices
            return self.func(self.arg[i])[indices]
        else:
            return self.func(self.arg[indices])
 
    def __iter__(self):
        raise TypeError
 
    @property
    def definition(self):
        x = self.arg
        return exp(x) / ReducedSum(exp(x))
 
    def _latex(self, p):
        return r"softmax\left(%s\right)" % p._print(self.arg)
 
     
softmax = Softmax


# https://tensorflow.google.cn/api_docs/python/tf/nn/relu?hl=en
def relu(x):
    return Max(x, 0)


relu = Function.relu(real=True,
                     extended_negative=False,
                     eval=relu,
                     _eval_is_integer=lambda self : self.arg.is_integer,
                     _eval_is_extended_positive=lambda self : self.arg.is_extended_positive
                     )


from . import convolutional