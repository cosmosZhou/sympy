from util import *


@apply
def apply(self):
    x, *limits = self.of(Lamda[Softmax])
    
    return Equal(self, Softmax(Lamda(x, *limits).simplify()), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(domain=Range(2, oo))
    m = Symbol(integer=True, positive=True)
    x = Symbol(shape=(m, n), real=True)
    i = Symbol(integer=True)
    Eq << apply(Lamda[i:m](Softmax(x[i])))

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    

    


if __name__ == '__main__':
    run()
# created on 2022-01-11
