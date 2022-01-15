from util import *


@apply
def apply(self, var=None):
    assert self.is_BlockMatrix
    axis = self.axis
    
    indices = []
    limits = []
    for i in range(axis + 1):
        j = self.generate_var({*indices}, integer=True, var=var)
        
        indices.append(j)
        limits.append((j, 0, self.shape[i]))
        
    limits.reverse()
    rhs = Lamda(self[tuple(indices)], *limits)
    
    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    n0, n1, n2, n3, m = Symbol(positive=True, integer=True, given=False)
    X0 = Symbol(shape=(m, n0), real=True)
    X1 = Symbol(shape=(m, n1), real=True)
    X2 = Symbol(shape=(m, n2), real=True)
    X3 = Symbol(shape=(m, n3), real=True)
    Eq << apply(BlockMatrix[1](X0, X1, X2, X3))

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    j = Symbol(domain=Range(n0 + n1 + n2 + n3))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)

    
    


if __name__ == '__main__':
    run()
# created on 2021-12-20
# updated on 2022-01-15
