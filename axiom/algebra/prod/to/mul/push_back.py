from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Product)

    assert i.is_integer
    back = function._subs(i, b)
    assert back.is_nonzero
    return Equal(self, Product[i:a:b + 1](function) / back, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    f, h = Function(real=True, positive=True)

    Eq << apply(Product[i:0:n](f(i) + h(i)))

    Eq << Eq[-1].this.rhs.find(Product).apply(algebra.prod.to.mul.split, cond={n})


if __name__ == '__main__':
    run()

# created on 2020-03-09
