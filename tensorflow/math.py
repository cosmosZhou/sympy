from sympy import Function, ReducedSum, exp, log

def logsumexp(x):
    return log(ReducedSum(exp(x)))

logsumexp = Function.logsumexp(shape=(), eval=logsumexp)
