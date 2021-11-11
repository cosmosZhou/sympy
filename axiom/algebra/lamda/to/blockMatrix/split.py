from util import *


@apply
def apply(self, k):
    f, *limits, (i, _0, m) = self.of(Lamda)
    assert 0 == _0    
    assert k <= m
    
    return Equal(self, BlockMatrix([Lamda[i:k](f, *limits), Lamda[i:m - k](f._subs(i, i + k), *limits)]), evaluate=False)

@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(m))
    f = Function(real=True)
    Eq << apply(Lamda[i:0:m](f(i)), k)

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    
    


if __name__ == '__main__':
    run()
# created on 2019-10-15
# updated on 2021-10-09