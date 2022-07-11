from util import *


@apply
def apply(self):
    function, *limits_d = self.of(Derivative)
    vars = [var for var, d in limits_d]
    
    args = function.of(Mul)
    coeff = []
    funcs = []
    for arg in args:
        if arg.has(*vars):
            funcs.append(arg)
        else:
            coeff.append(arg)
    coeff = Mul(*coeff)
    funcs = Mul(*funcs)
    return Equal(self, coeff * Derivative(funcs, *limits_d))


@prove(proved=False)
def prove(Eq):
    x, h = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Derivative[x](f(x) * h))


if __name__ == '__main__':
    run()
# created on 2022-01-25
