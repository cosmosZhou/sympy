from sympy.core.function import Function

@Function(shape=property(lambda self: self.arg.shape[:-1]), is_finite=True)
def logsumexp(x):
    from sympy.concrete.reduced import ReducedSum
    from sympy.functions.elementary.exponential import Exp, log
    return log(ReducedSum(Exp(x)))
'''	
from sympy.core.function import Function
from sympy.concrete.reduced import ReducedSum
from sympy.functions.elementary.exponential import Exp, log
    

class LogSumExp(Function):
    r"""
    x is a vector
    LogSumExp(x) = log(ReducedSum(exp(x)))
    """

    def _eval_is_finite(self):
        return True
    
    def _eval_is_extended_real(self):
        return self.arg.is_extended_real

    @classmethod
    def eval(cls, arg):
        ...
#         return log(ReducedSum(Exp(arg)))
 
    def simplify(self, **_):
        return self
 
#     def __getitem__(self, indices):
#         ...
 
#     def __iter__(self):
#         raise TypeError
 
#     def _latex(self, p):
#         return r"softmax\left(%s\right)" % p._print(self.arg)
 
    @property
    def shape(self):
        return self.arg.shape[:-1]
     
logsumexp = LogSumExp
    
'''