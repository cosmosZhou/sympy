from sympy import Function, ReducedSum, exp, log

def logsumexp(x):
    return log(ReducedSum(exp(x)))

def shape(self):
    return self.arg.shape[:-1]

logsumexp = Function(logsumexp, shape=property(shape), is_finite=True)
