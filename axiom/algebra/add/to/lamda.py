from util import *


def to_Lamda(self, expr, deep=False):
    variables = self.variables    
    if expr.shape:
        size = min(len(expr.shape), len(variables))
        variables = variables[:size]
        expr = expr[variables[::-1]]
        if deep and expr.is_Lamda:
            expr = to_Lamda(expr, self.expr)
        else:
            expr += self.expr
    else:
        expr += self.expr
        
    return Lamda(expr, *self.limits)
    
@apply
def apply(self, deep=False):
    [*args] = self.of(Add)
    for i, lamda in enumerate(args):
        if lamda.is_Lamda:
            del args[i]
            rhs = to_Lamda(lamda, Add(*args), deep=deep)
            break
    else:
        for i, lamda in enumerate(args):
            lamda = lamda.of(-Lamda)
            if lamda:
                expr, *limits = lamda
                lamda = Lamda(-expr, *limits)
                del args[i]
                rhs = to_Lamda(lamda, Add(*args), deep=deep)
                break          
        else:
            return
        
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(integer=True)
    g = Symbol(shape=(n, n), integer=True)
    Eq << apply(Lamda[i:n, j:n](f(j, i)) + g)

    i, j = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)

    
    


if __name__ == '__main__':
    run()
# created on 2018-04-04
# updated on 2021-11-21