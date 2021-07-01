from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Product[Tuple])
    
    assert i.is_integer
    back = function._subs(i, b)
    assert back.is_nonzero
    return Equal(self, Product[i:a:b + 1](function) / back, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)

    f = Function.f(real=True, positive=True)
    h = Function.h(real=True, positive=True)

    Eq << apply(Product[i:0:n](f(i) + h(i)))

    Eq << Eq[-1].this.rhs.find(Product).apply(algebra.product.to.mul.split, cond={n})


if __name__ == '__main__':
    run()

