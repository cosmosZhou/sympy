from util import *


@apply
def apply(self, evaluate=True): 
    expr, (x, x0, dir) = self.of(Limit)
    args = expr.of(Mul)
    
    coefficient = []
    factors = []
    for arg in args:
        if arg._has(x):
            factors.append(arg)
        else:
            coefficient.append(arg)
    
    coefficient = Mul(*coefficient)
    factors = Mul(*factors)
    
    limited = Limit[x:x0:dir](factors)
    if evaluate:
        limited = limited.doit()
    return Equal(self, coefficient * limited)


@prove(proved=False)
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    
    Eq << apply(Limit[x:x0](f(x) * y))    

    
if __name__ == '__main__':
    run()
