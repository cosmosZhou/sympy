from util import *


@apply
def apply(given):
    n, b = given.of(Less)
    assert n.is_integer
    return Contains(n, Range(-oo, b))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    
    Eq << apply(n < b)
    
    Eq << Eq[-1].simplify()
    

if __name__ == '__main__':
    run()

