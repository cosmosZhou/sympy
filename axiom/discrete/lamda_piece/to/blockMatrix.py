from util import *


@apply
def apply(self):
    ecs, *limits, (i, _0, n) = self.of(Lamda[Piecewise])
    args = []
    
    index = 0
    for e, c in ecs:
        if c:
            X = Lamda(e, *limits, (i, index, n)).simplify()
        else:
            _i, rows = c.of(Less)
            assert _i == i
            X = Lamda(e, *limits, (i, index, rows)).simplify()
            
        args.append(X)
        index = rows
    
    return Equal(self, BlockMatrix(args))


@prove
def prove(Eq):
    from axiom import algebra

    n0, n1, n2, n3, m = Symbol(positive=True, integer=True, given=False)
    X0 = Symbol(shape=(n0, m), real=True)
    X1 = Symbol(shape=(n1, m), real=True)
    X2 = Symbol(shape=(n2, m), real=True)
    X3 = Symbol(shape=(n3, m), real=True)
    i = Symbol(integer=True)
    Eq << apply(Lamda[i:n0 + n1 + n2 + n3](Piecewise((X0[i], i < n0), (X1[i - n0], i < n0 + n1), (X2[i - n0 - n1], i < n0 + n1 + n2), (X3[i - n0 - n1 - n2], True))))

    i = Symbol(domain=Range(n0 + n1 + n2 + n3))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    
    


if __name__ == '__main__':
    run()
# created on 2021-10-04
# updated on 2021-10-04