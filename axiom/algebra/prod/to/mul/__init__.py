from util import *


@apply
def apply(self, simplify=True):
    from axiom.algebra.sum.to.add import associate
    return Equal(self, associate(Product, self, simplify=simplify))


@prove(provable=False)
def prove(Eq):
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h = Function(real=True)
    Eq << apply(Product[i:n](f(i) * h(i)))


if __name__ == '__main__':
    run()

from . import push_back
from . import split
from . import doit
from . import push_front
# created on 2018-04-14
