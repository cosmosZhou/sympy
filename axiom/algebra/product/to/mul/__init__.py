from util import *


@apply
def apply(self, simplify=True):
    from axiom.algebra.sum.to.add import associate
    return Equal(self, associate(Product, self, simplify=simplify))


@prove(provable=False)
def prove(Eq):
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)

    f = Function.f(real=True)
    h = Function.h(real=True)

    Eq << apply(Product[i:n](f(i) * h(i)))


if __name__ == '__main__':
    run()

from . import st
from . import doit
from . import push_front
from . import push_back
from . import split
