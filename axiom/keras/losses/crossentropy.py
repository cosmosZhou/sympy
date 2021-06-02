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
    from axiom import calculus, algebra
    n = Symbol.n(domain=Range(2, oo))
    t = Symbol.t(shape=(n,), real=True)
    j = Symbol.j(integer=True)

    Eq << apply(Equal(Sum[j](t[j]), 1))
    assert Eq[0].lhs.is_zero == False

    Eq << Eq[-1].lhs.expr.this.defun()

    Eq << Eq[-1].this.rhs.args[1].expand(var=j)

    i = Symbol.i(domain=Range(0, n))
    xi = Eq[2].lhs._wrt_variables[0][i]

    assert Eq[-1].lhs.has(xi)

    Eq << Eq[-1].apply(calculus.eq.imply.eq.derive, (xi,), simplify=False)

    Eq.loss = Eq[-1].this.rhs.doit(deep=False)

    i = xi.indices[0]
    Eq << Eq[0][i]

    Eq << Eq[0][j]

    assert Eq[0].lhs.is_zero == False

    assert Eq[-1].lhs.is_zero == False

    Eq << Eq[-1].apply(calculus.eq.imply.eq.derive, (xi,), simplify=False)

    assert Eq[-1].lhs.expr.is_zero == False

    Eq << Eq[-1].this.rhs.doit(deep=False)

    assert Eq[-1].lhs.expr.is_zero == False

    Eq << Eq[-1].subs(Eq[-3].reversed).subs(Eq[-4].reversed) / Eq[-1].lhs.expr

    Eq.loss = Eq.loss.subs(Eq[-1]).expand()

    Eq.loss = Eq.loss.this.rhs.args[0].simplify()

    Eq.loss = Eq.loss.this.rhs.args[1].args[1].simplify()

    Eq.loss = Eq.loss.subs(Eq[1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq.loss, (i,), simplify=False)


if __name__ == '__main__':
    run()
