from util import *
import axiom



@apply
def apply(x):    
    n = x.generate_var(integer=True, var='n')
    return Equal(E ** x, Sum[n:oo](x ** n / factorial(n)))


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(x)

if __name__ == '__main__':
    run()

