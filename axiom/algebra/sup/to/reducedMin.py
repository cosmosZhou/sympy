from util import *


@apply
def apply(self, y=None): 
    expr, *limits = self.of(Sup)
    if y is None:
        y = self.generate_var(real=True, var='y')
    
    return Equal(self, ReducedMin({y: ForAll(expr <= y, *limits)}))


@prove(provable=False)
def prove(Eq):
    x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:m:M](f(x)))


if __name__ == '__main__':
    run()