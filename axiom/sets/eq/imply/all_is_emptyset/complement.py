from util import *


@apply
def apply(given, excludes=None):
    from sympy.concrete.limits import limits_dict

    (xi, *limits), (_xi, *_limits) = given.of(Equal[Abs[Cup], Sum[Abs]])

    assert xi == _xi
    assert limits == _limits

    limitsDict = limits_dict(limits)
    i, *_ = limitsDict.keys()

    kwargs = i._assumptions.copy()
    if 'domain' in kwargs:
        del kwargs['domain']

    j = xi.generate_var(excludes=excludes, **kwargs)
    xj = xi.subs(i, j)

    i_domain = limitsDict[i] or i.domain

    limits = [(j, i_domain - {i})] + [*limits]
    return All(Equal(xi & xj, xi.etype.emptySet).simplify(), *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol.i(integer=True)
    k = Symbol.k(integer=True, positive=True, given=True)
    j = Symbol.j(domain=Range(0, k + 1) - {i})
    assert j <= k
    assert k >= j
    assert (j - k).is_nonpositive
    assert (k - j).is_nonnegative
    x = Symbol.x(shape=(k + 1,), etype=dtype.integer, finite=True, given=True)
    Eq << apply(Equal(abs(Cup[i:0:k](x[i])), Sum[i:0:k](abs(x[i]))))

    j = Eq[-1].variables[0]
    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(sets.is_nonemptyset.imply.is_positive)

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(x[i], x[j])

    Eq << Eq[-2].this.expr.apply(algebra.eq.gt.imply.lt.subs, Eq[-1])

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[-1], simplify=False)

    Eq.gt = Eq[-1].this.expr.apply(algebra.eq.lt.imply.gt.substract)

    Eq << Eq[0].lhs.arg.this.apply(sets.cup.to.union.split, cond={i, j})

    Eq.union_less_than = sets.imply.le.cup.apply(x[i], *Eq[-1].rhs.args[0].limits)

    Eq << sets.imply.le.union.apply(*Eq[-1].rhs.args)

    Eq << Eq.gt.this.expr.apply(algebra.gt.le.imply.gt.subs, Eq[-1])

    Eq << Eq[-1].this().expr.simplify()

    Eq << Eq[-1].this.find(Abs + Abs[~Cup]).apply(sets.cup.to.union.doit.setlimit)

    Eq << Eq.union_less_than.this.find(Cup).limits_subs(Eq.union_less_than.find(Cup).variable, Eq[-1].find(Cup).variable)

    Eq << Eq[-1].this.expr.apply(algebra.gt.le.imply.gt.subs, Eq.union_less_than)

    Eq << Eq[-1].this().expr.lhs.simplify()

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], index=0, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(sets.contains.imply.ne)

    Eq << Eq[-1].this.expr.apply(algebra.ne.cond.imply.cond.subs)


if __name__ == '__main__':
    run()

