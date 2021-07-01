from util import *


@apply
def apply(a):
    n = a.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    return Equal(Det(Lamda[j:n, i:n](a[j] ** i)), Product[j:i, i:n](a[i] - a[j]))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol.n(domain=Range(2, oo), given=False)
    a = Symbol.a(shape=(oo,), complex=True)
    Eq << apply(a[:n])

    Eq.initial = Eq[-1].subs(n, 2)

    Eq << Eq.initial.this.rhs.doit(deep=True)

    Eq << Eq[-1].this.lhs.arg.apply(algebra.lamda.to.matrix).this.lhs.doit()

    Eq.induct = Eq[0].subs(n, n + 1)

    D = Eq.induct.lhs.arg
    def row_transformation(a, *limits):
        n = limits[0][-1]
        (i, *_), (j, *_) = limits
        return Identity(n) - Lamda[j:n, i:n](a[0] * KroneckerDelta(i, j + 1))
    Eq.expand = (row_transformation(a, *D.limits) @ D).this.apply(discrete.matmul.to.lamda)

    Eq << discrete.matrix.determinant.expansion_by_minors.apply(Eq.expand.rhs, i=0)

    Eq << Eq[-1].this.rhs.split(slice(0, 1))

    Eq << Eq[-1].this.rhs.args[0].args[0].arg().function.simplify()

    Eq << Eq[-1].this.rhs.args[0].args[1].doit()

    Eq.recursion = Eq[-1].this.rhs.args[1].function.args[-1].doit()

    Eq << Eq.recursion.rhs.args[0].arg.this.function.doit()

    Eq << Eq[-1].this.rhs().function.simplify()

    Eq << Eq[-1].this.function.rhs.expand().this.function.rhs.collect(Eq[-1].rhs.args[1].args[-1])

    Eq.recursion = algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq.recursion)

    Eq << Eq.recursion.rhs.args[1].function.args[1].arg.this.function.args[0].expr.doit()

    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=Eq[-1].rhs.variable)

    Eq << Eq[-1].this.function.rhs.args[0].expr.expand().this.function.rhs.args[0].expr.collect(Eq[-1].rhs.args[0][0].args[1].args[-1])

    Eq.recursion = algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq.recursion)

    Eq << Eq.recursion.rhs.args[0].arg.this.apply(algebra.lamda.to.mul)

    Eq << Eq[-1].apply(discrete.eq.imply.eq.det)

    i = Eq[-1].rhs.args[1].variable
    Eq.determinant = Eq[-1].this.rhs.args[1].limits_subs(i, i - 1)

    k, _ = Eq.determinant.lhs.arg.variables
    j, i = Eq[0].lhs.arg.variables
    Eq << algebra.eq.imply.eq.subs.apply(Eq[0], a[:n], a[1:n + 1])

    Eq << Eq[-1].this.lhs.arg.limits_subs(j, k).this.lhs.arg.limits_subs(i, j).this.rhs.limits_subs(i, i - 1)

    Eq << Eq[-1].this.rhs.limits_subs(j, j - 1)

    Eq << Eq.determinant.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.product)

    Eq << Eq[-1].this.rhs.function.apply(algebra.mul.to.product.limits.push_front)

    Eq << Product[j:i, i:n + 1](Eq[0].rhs.function).this.split(slice(0, 1))

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.recursion = Eq.recursion.subs(Eq[-1])

    D = Eq.recursion.rhs.args[1].function.args[1].arg
    _i = i.copy(positive=True)
    D = D._subs(i, _i)
    Eq << discrete.matrix.determinant.expansion_by_minors.apply(D, j=0).forall((_i,))

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq.recursion)

    Eq << Eq.expand.apply(discrete.eq.imply.eq.det)
    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1].this.lhs.args[0].doit()
    

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=2)


if __name__ == '__main__':
    run()

from . import concat
from . import matmul_equal
