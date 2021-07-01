from util import *


@apply
def apply(given):
    function, limit = given.of(Equal[Sum, 1])

    if len(limit) == 1:
        j = limit[0]
        a, b = function.domain_defined(j).of(Range)
    else:
        j, a, b = limit

    n = b - a

    t = Lamda[j:0:n](function).simplify()

    assert n >= 2

    x = Symbol.x(shape=(n,), real=True)
    y = Symbol.y(softmax(x))

    assert y.is_zero == False

    return Equal(Derivative(crossentropy(t, y), x), y - t)


@prove
def prove(Eq):
    from axiom import discrete, calculus, algebra

    n = Symbol.n(domain=Range(2, oo))
    t = Symbol.t(shape=(n,), real=True)
    j = Symbol.j(integer=True)
    Eq << apply(Equal(Sum[j](t[j]), 1))

    Eq << Eq[-1].lhs.expr.this.defun()

    Eq << Eq[-1].this.rhs.args[1].apply(discrete.matmul.to.sum, var=j)

    i = Symbol.i(domain=Range(0, n))
    xi = Eq[2].lhs.variable[i]
    Eq << Eq[-1].apply(calculus.eq.imply.eq.derive, (xi,), simplify=False)

    Eq << Eq[-1].this.rhs.doit(deep=False)

    Eq.loss = Eq[-1].this.find(Derivative[Sum]).apply(calculus.derivative.to.sum)

    i = xi.indices[0]
    Eq << Eq[0][i]

    Eq << Eq[0][j]

    Eq << Eq[-1].apply(calculus.eq.imply.eq.derive, (xi,), simplify=False)

    Eq << Eq[-1].this.rhs.doit(deep=False)

    Eq << Eq[-1].subs(Eq[-3].reversed).subs(Eq[-4].reversed) / Eq[-1].lhs.expr

    Eq << Eq.loss.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.args[0].simplify()

    Eq << Eq[-1].this.rhs.args[1].args[1].simplify()

    Eq << Eq[-1].subs(Eq[1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i,), simplify=False)


if __name__ == '__main__':
    run()
