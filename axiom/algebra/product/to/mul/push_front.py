from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Product[Tuple])
    assert i.is_integer     
    front = function._subs(i, a - 1)
    assert front.is_nonzero
    return Equal(self, Product[i:a - 1:b](function) / front, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    C = Symbol.C(etype=dtype.integer, given=True)

    f = Function.f(real=True, positive=True)
    h = Function.h(real=True, positive=True)

    Eq << apply(Product[i:1:n](f(i) + h(i)))

    Eq << Eq[-1].this.rhs.find(Product).apply(algebra.product.to.mul.split, cond={0})


if __name__ == '__main__':
    run()

