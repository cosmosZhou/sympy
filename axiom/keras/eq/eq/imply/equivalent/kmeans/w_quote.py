from util import *

from axiom.keras.eq.eq.imply.eq.kmeans.nonoverlapping import cluster, mean


@apply
def apply(eq_sum, eq_union, x=None):
    w_sum, M = eq_sum.of(Equal)
    w_union, M_interval = eq_union.of(Equal)

    zero, _M = M_interval.of(Range)
    assert _M == M
    assert zero == 0

    wi_abs, limit = w_sum.of(Sum)
    wi, _limit = w_union.of(Cup)

    assert limit == _limit

    _wi = wi_abs.of(Card)
    assert _wi == wi

    (i,) = limit
    w, _i = wi.of(Indexed)
    assert _i == i

    _M = x.shape[0]
    assert _M == M

    j = Symbol(integer=True)

    k = w.shape[0]
    w_ = Symbol("omega^'", cluster(w, x))

    c = Lamda[i](mean(w[i], x))

    return Equivalent(Element(j, w_[i]) & Element(i, Range(0, k)),
                      Equal(i, ArgMin[i](Norm(x[j] - c[i]))) & Element(j, Range(0, M)))


@prove
def prove(Eq):
    from axiom import keras

    M, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    k = Symbol(domain=Range(0, M))
    x = Symbol(real=True, shape=(M, n))
    w = Symbol(shape=(k,), etype=dtype.integer, empty=False)
    Eq << apply(Equal(Sum[i](Card(w[i])), M), Equal(Cup[i](w[i]), k.domain), x=x)

    Eq << keras.eq.eq.imply.eq.kmeans.nonoverlapping.apply(Eq[0], Eq[1], x=x)

    Eq << keras.eq.eq.imply.equivalent.kmeans.apply(Eq[-2], Eq[-1], x=x)

    Eq << Eq[-1].this.find(Bool).arg.rhs.base.definition

    Eq << Eq[-1].this.find(Bool).arg.rhs.base.defun()


if __name__ == '__main__':
    run()
