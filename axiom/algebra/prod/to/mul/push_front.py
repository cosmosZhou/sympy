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
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    C = Symbol(etype=dtype.integer, given=True)

    f, h = Function(real=True, positive=True)

    Eq << apply(Product[i:1:n](f(i) + h(i)))

    Eq << Eq[-1].this.rhs.find(Product).apply(algebra.prod.to.mul.split, cond={0})


if __name__ == '__main__':
    run()

# created on 2020-03-10
