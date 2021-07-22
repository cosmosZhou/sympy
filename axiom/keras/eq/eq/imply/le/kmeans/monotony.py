from util import *


@apply
def apply(eq_sum, eq_union, x=None):
    ((_w, ___i), i), M = eq_sum.of(Equal[Sum[Abs[Indexed], Tuple]])
    ((w, __i), _i), (zero, _M) = eq_union.of(Equal[Cup[Indexed, Tuple], Range])

    assert _M == M
    assert zero == 0

    assert i == _i == __i == ___i
    assert _w == w

    assert x.shape[0] == M

    w_ = Symbol("omega^'", cluster(w, x))

    j = Symbol.j(integer=True)

    return LessEqual(Sum[j:w_[i], i](Norm(x[j] - mean(w_[i], x)) ** 2),
                     Sum[j:w[i], i](Norm(x[j] - mean(w[i], x)) ** 2))


from axiom.keras.eq.eq.imply.eq.kmeans.nonoverlapping import cluster, mean


@prove(proved=False)
def prove(Eq):
    from axiom import keras, algebra, sets

    M = Symbol.M(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    k = Symbol.k(domain=Range(0, M))
    x = Symbol.x(real=True, shape=(M, n))
    w = Symbol.omega(shape=(k,), etype=dtype.integer, emptyset=False)
    Eq << apply(Equal(Sum[i](abs(w[i])), M), Equal(Cup[i](w[i]), k.domain), x=x)

    Eq << keras.eq.eq.imply.equivalent.kmeans.apply(Eq[1], Eq[2], x=x)

    Eq << algebra.equivalent.imply.eq.sum.collapse.apply(Eq[-1], Eq[3].rhs.expr)

    i_ = Symbol.i(Eq[-1].find(Indexed, Sum))
    Eq << Eq[-1].subs(i_.this.definition.reversed)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.domain_defined.delete)

    Eq.plausible = Eq[3].subs(Eq[-1])

    Eq << keras.eq.eq.imply.equivalent.kmeans.w_quote.apply(Eq[1], Eq[2], x=x)

    Eq << algebra.equivalent.imply.eq.sum.collapse.apply(Eq[-1], Eq.plausible.lhs.expr)

    i__ = Symbol("i'", Eq[-1].find(Indexed, ArgMin))
    Eq << Eq[-1].subs(i__.this.definition.reversed)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.domain_defined.delete)

    Eq.plausible = Eq.plausible.subs(Eq[-1])

    Eq << Eq.plausible.this.find(Norm).apply(algebra.norm.to.sqrt)

    Eq.le = Eq[-1].this.find(Norm).apply(algebra.norm.to.sqrt)

    Eq << Eq.le.find(mean, Indexed).this.definition

    Eq << Eq[-1].this.rhs.definition

    Eq << sets.eq.imply.all.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.imply.le.st.argmin)

    Eq << Eq[-1].this.expr.apply(algebra.le.imply.le.square)

    Eq << Eq[-1].this.find(Norm).apply(algebra.norm.to.sqrt)

    Eq << Eq[-1].this.find(Norm).apply(algebra.norm.to.sqrt)

    Eq << Eq.le.find(mean).this.defun()

    Eq << Eq[-1][i]

    Eq << Eq.le.rhs.find(mean).this.defun()

    Eq << Eq[-1][i]

    Eq << Eq.le.subs(Eq[-1], Eq[-3])

    Eq << algebra.le.given.is_nonnegative.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.sum.subtract)

    Eq << Eq[-1].this.lhs.expr.expand()

    Eq << algebra.is_nonnegative.given.is_nonnegative.st.sum.apply(Eq[-1])


if __name__ == '__main__':
    run()
