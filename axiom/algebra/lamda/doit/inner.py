from util import *


def doit(self):
    xi, (i, a, b), *limits = self.of(Lamda[Tuple])
    assert i.is_integer

    diff = b - a
    assert diff == int(diff)

    arr = [xi._subs(i, a + t) for t in range(diff)]
    
    assert limits, "try to invoke algebra.lamda.to.matrix"
    return Lamda(BlockMatrix(arr), *limits)


@apply
def apply(self):
    return Equal(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = 5
    Eq << apply(Lamda[j:n, i:m](x[i, j]))

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    Eq << Eq[-1].this.lhs.apply(algebra.lamda.to.matrix)

    


if __name__ == '__main__':
    run()
# created on 2022-07-08
