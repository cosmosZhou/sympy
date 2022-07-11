from util import *


@apply
def apply(self, axis=-1):
    if axis < 0:
        axis += len(self.shape)

    if axis == self.default_axis:
        f, j_limit, i_limit, *limits = self.of(Lamda)
        assert not f.shape
        expr = Lamda(f, i_limit, j_limit, *limits).simplify()
    elif axis == 1:
        f, *limits, j_limit, i_limit = self.of(Lamda)
        expr = Lamda(f, *limits, i_limit, j_limit).simplify()
    return Equal(self, Transpose[axis](expr, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, j, k = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    h = Symbol(real=True, shape=(oo, m))
    Eq << apply(Lamda[j:n, i:m](h[j + k, i]))

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    
    


if __name__ == '__main__':
    run()
# created on 2022-01-11

from . import block
# updated on 2022-03-30
