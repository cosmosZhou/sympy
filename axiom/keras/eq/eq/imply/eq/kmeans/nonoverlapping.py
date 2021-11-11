from util import *


@apply
def apply(eq_sum, eq_union, x=None):
    w_sum, M = eq_sum.of(Equal)
    w_union, M_interval = eq_union.of(Equal)

    zero, _M = M_interval.of(Range)
    assert _M == M
    assert zero == 0

    _wi, i = w_sum.of(Sum[Card, Tuple])
    wi, _i = w_union.of(Cup[Tuple])

    assert i == _i
    assert _wi == wi

    w, _i = wi.of(Indexed)
    assert _i == i

    assert x.shape[0] == M

    w_ = Symbol("omega^'", cluster(w, x))

    return Equal(Sum[i](Card(w_[i])), M), Equal(Cup[i](w_[i]), M_interval)


def mean(wi, x):
    j = Symbol(integer=True)
    return Sum[j:wi](x[j]) / Card(wi)


def __getitem__(self, indices):
    if isinstance(indices, (tuple, list)):
        return Indexed(self, *indices)
    return Indexed(self, indices)


mean = Function.mean(shape=property(lambda self: self.args[1].shape[1:]), real=True, eval=mean, __getitem__=__getitem__)


# c is a list of vectors, (k, n)
# return a list of set of integers, (k,)
def cluster(w, x):
    i, j = Symbol(integer=True)
    k = w.shape[0]
    return Lamda[i:k](conditionset(j, Equal(ArgMin[i](Norm(x[j] - mean(w[i], x))), i)))


cluster = Function.cluster(eval=cluster, __getitem__=__getitem__)


@prove
def prove(Eq):
    from axiom import sets

    M, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    k = Symbol(domain=Range(M))
    x = Symbol(real=True, shape=(M, n))
    w = Symbol(shape=(k,), etype=dtype.integer, empty=False)
    Eq << apply(Equal(Sum[i](Card(w[i])), M), Equal(Cup[i](w[i]), k.domain), x=x)

    Eq << Eq[2].this.rhs.defun()

    Eq.omega_i_definition0 = Eq[-1][i]

    Eq.omega_i_definition = Eq.omega_i_definition0.this.rhs.apply(sets.conditionset.rewrite.domain_defined)

    j = Eq.omega_i_definition.rhs.variable
    Eq << sets.eq.given.et.infer.apply(Eq[4], wrt=j)

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.imply.any_el), \
    Eq[-1].this.rhs.apply(sets.el_cup.given.any_el)

    Eq <<= Eq[-2].subs(Eq.omega_i_definition), Eq[-1].subs(Eq.omega_i_definition0)

    Eq << Eq[-2].this.lhs.expr.simplify()

    Eq << Eq[-1].this.rhs.expr.simplify()

    w_ = Eq.omega_i_definition.lhs.base
    k_ = Symbol(integer=True)
    Eq.nonoverlapping = All[i:k_](Equal(w_[i] & w_[k_], w_[i].etype.emptySet), plausible=True)

    Eq << Eq.omega_i_definition0.subs(i, k_)

    Eq << sets.eq.eq.imply.eq.intersect.apply(Eq.omega_i_definition0, Eq[-1])

    Eq << Eq[-1].this.find(And).apply(sets.eq.eq.imply.el.finiteset)

    Eq << Eq.nonoverlapping.subs(Eq[-1])

    Eq << Eq[-1].this().find(Intersection).simplify()

    Eq << sets.all_is_empty.imply.eq.nonoverlapping.intlimit.utility.apply(Eq.nonoverlapping, k)

    Eq << Eq[-1].this.find(Cup).limits_subs(k_, i)

    Eq << Eq[-1].this.rhs.limits_subs(k_, i)

    Eq << Eq[-1].subs(Eq[4]).reversed


if __name__ == '__main__':
    run()
# created on 2020-12-24
# updated on 2020-12-24
