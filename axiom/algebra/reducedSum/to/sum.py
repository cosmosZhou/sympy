from util import *


@apply
def apply(self, i=None):
    if i is None:
        i = self.arg.generate_var(integer=True)
    
    [n] = self.arg.shape
    rhs = Sum[i:n](self.arg[i])    
        
    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    y = Symbol.y(shape=(n,), real=True)
    Eq << apply(ReducedSum(y))


if __name__ == '__main__':
    run()