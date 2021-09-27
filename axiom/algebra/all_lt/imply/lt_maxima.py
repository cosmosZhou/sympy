from util import *


@apply
def apply(given): 
    (fx, M), *limits = given.of(All[Less])
    return Maxima(fx, *limits) < M


@prove
def prove(Eq):
    
    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b](f(x) < M))
    
    


if __name__ == '__main__':
    run()