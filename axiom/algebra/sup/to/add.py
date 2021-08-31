from util import *


@apply
def apply(self): 
    expr, *limits = self.of(Sup)
    vars = [x for x, *ab in limits]
    const = []
    args = []
    for arg in expr.of(Add):
        if arg.has(*vars):
            args.append(arg)
        else:
            const.append(arg)
    assert const
    
    const = Add(*const)
    expr = Add(*args)
    
    return Equal(self, const + Sup(expr, *limits))


@prove
def prove(Eq):
    x, m, h = Symbol(real=True)
    f = Function(real=True)
    M = Symbol(domain=Interval(m, oo, left_open=True))
    Eq << apply(Sup[x:m:M](f(x) + h))


if __name__ == '__main__':
    run()