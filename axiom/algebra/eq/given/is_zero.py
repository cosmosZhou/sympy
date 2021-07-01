from util import *


@apply(simplify=False)
def apply(given): 
    x, y = given.of(Equal)
        
    return Equal(x - y, 0)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True, zero=False)
    Eq << apply(Equal(a, b))
    
    Eq << Eq[1] + b
    
    
if __name__ == '__main__':
    run()
