from util import *


@apply
def apply(eq):
    (x, (hx, fx)), gx = eq.of(Equal[Symbol + Mul[sigmoid]])
    assert x.is_symbol
    assert gx._has(x) and fx._has(x) and hx._has(x)
    [n] = x.shape
    return Equal(
        Derivative[x](gx),
        Identity(*x.shape) + (Derivative[x](fx) * (1 - sigmoid(fx)) * Identity(n) * hx + Derivative[x](hx)) * sigmoid(fx))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    f, g, h = Function(real=True, shape=(n,))
    Eq << apply(Equal(g(x), x + h(x) * sigmoid(f(x))))

    Eq << calculus.eq.imply.eq.derive.apply(Eq[0], (x,))

    Eq << Eq[-1].this.rhs.apply(calculus.derivative.to.add)

    Eq << Eq[-1].this.find(Derivative[sigmoid]).apply(calculus.derivative_sigmoid.to.mul.sigmoid.vector)

    Eq << Eq[-1].this.rhs.apply(algebra.add.collect)

    
    


if __name__ == '__main__':
    run()
# created on 2021-12-22
# updated on 2022-01-01