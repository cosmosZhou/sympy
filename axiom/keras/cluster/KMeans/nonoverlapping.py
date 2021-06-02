from util import *


@apply
def apply(*given, x=None):
    import axiom
    eq_sum, eq_union = given
    w_sum, M = eq_sum.of(Equal)
    w_union, M_interval = eq_union.of(Equal)

    zero, _M = M_interval.of(Range)
    assert _M == M
    assert zero == 0

    wi_abs, limit = w_sum.of(Sum)
    wi, _limit = w_union.of(Cup)

    assert limit == _limit

    _wi = wi_abs.of(Abs)
    assert _wi == wi

    (i,) = limit
    w, _i = wi.of(Indexed)
    assert _i == i

    _M = x.shape[0]
    assert _M == M

    w_ = Symbol("omega^'", cluster(w, x))

    return Equal(Sum[i](abs(w_[i])), M), Equal(Cup[i](w_[i]), M_interval)


def mean(wi, x):
    j = Symbol.j(integer=True)
    return Sum[j:wi](x[j]) / abs(wi)


def __getitem__(self, indices):
    if isinstance(indices, (tuple, list)):
        return Indexed(self, *indices)
    return Indexed(self, indices)


mean = Function.mean(shape=property(lambda self: self.args[1].shape[1:]), real=True, eval=mean, __getitem__=__getitem__)


# c is a list of vectors, (k, n)
# return a list of set of integers, (k,)
def cluster(w, x):
    i = Symbol.i(integer=True)
    k = w.shape[0]
    j = Symbol.j(integer=True)

    return Lamda[i:k](conditionset(j, Equal(ArgMin[i](Norm(x[j] - mean(w[i], x))), i)))


cluster = Function.cluster(eval=cluster, __getitem__=__getitem__)


@prove
def prove(Eq):
    from axiom import sets
    M = Symbol.M(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)

    k = Symbol.k(domain=Range(0, M))

    x = Symbol.x(real=True, shape=(M, n))
    w = Symbol.omega(shape=(k,), etype=dtype.integer, emptyset=False)

    Eq << apply(Equal(Sum[i](abs(w[i])), M), Equal(Cup[i](w[i]), k.domain), x=x)

    Eq << Eq[0].this.rhs.defun()

    Eq.omega_i_definition0 = Eq[-1][i]

    Eq.omega_i_definition = Eq.omega_i_definition0.this.rhs.apply(sets.conditionset.rewrite.domain_defined)

    j = Eq.omega_i_definition.rhs.variable
    Eq << sets.eq.given.suffice.apply(Eq[4], wrt=j)

    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.any_contains.st.cup), \
    Eq[-1].this.rhs.apply(sets.contains.given.any_contains.st.cup)

    Eq <<= Eq[-2].subs(Eq.omega_i_definition), Eq[-1].subs(Eq.omega_i_definition0)

    Eq << Eq[-2].this.lhs.function.simplify()

    Eq << Eq[-1].this.rhs.function.simplify()

    w_ = Eq.omega_i_definition.lhs.base

    k_ = Symbol.k(integer=True)

    Eq.nonoverlapping = ForAll[i:k_](Equal(w_[i] & w_[k_], w_[i].etype.emptySet), plausible=True)

    Eq << Eq.omega_i_definition0.subs(i, k_)

    Eq << sets.eq.eq.imply.eq.intersection.apply(Eq.omega_i_definition0, Eq[-1])

    Eq << Eq[-1].this.find(And).apply(sets.eq.eq.imply.contains.finiteset)

    Eq << Eq.nonoverlapping.subs(Eq[-1])

    Eq << Eq[-1].this().find(Intersection).simplify()

    Eq << sets.all_is_emptyset.imply.eq.nonoverlapping.util.intlimit.apply(Eq.nonoverlapping, k)

    Eq << Eq[-1].this.find(Cup).limits_subs(k_, i)

    Eq << Eq[-1].this.rhs.limits_subs(k_, i)

    Eq << Eq[-1].subs(Eq[4]).reversed


if __name__ == '__main__':
    run()
