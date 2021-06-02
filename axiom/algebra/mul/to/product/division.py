from util import *
import axiom



@apply
def apply(self):
    fx, gx = axiom.is_Divide(self)
    fx, *limits = fx.of(Product)
    gx, *_limits = gx.of(Product)

    assert limits == _limits

    return Equal(self, Product(fx / gx, *limits))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(Product[k:n](f(k)) / Product[k:n](g(k)))

    Eq << Eq[0].this.find(1 / Product).apply(algebra.pow.to.product)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.product)


if __name__ == '__main__':
    run()
