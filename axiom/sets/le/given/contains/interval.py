from util import *


@apply(simplify=False)
def apply(given):
    n, b = given.of(LessEqual)

    return Contains(n, Interval(-oo, b))


@prove
def prove(Eq):
    n = Symbol.n(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    Eq << apply(n <= b)
    
    Eq << Eq[-1].simplify()
    

if __name__ == '__main__':
    run()

