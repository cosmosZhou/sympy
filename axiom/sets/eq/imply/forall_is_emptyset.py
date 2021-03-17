from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre

# given: |Union x[i]| = Sum |x[i]|
# x[i] & x[j] = Ø


@apply
def apply(given, excludes=None):
    assert given.is_Equality
    x_union_abs, x_abs_sum = given.args
    if not x_union_abs.is_Abs:
        tmp = x_union_abs
        x_union_abs = x_abs_sum
        x_abs_sum = tmp
        assert x_union_abs.is_Abs

    x_union = x_union_abs.arg
    assert x_union.is_UNION
    if x_abs_sum.is_Sum:
        assert x_abs_sum.function.is_Abs
        assert x_abs_sum.function.arg == x_union.function        
    else: 
        assert x_abs_sum == summation(abs(x_union.function), *x_union.limits)

    limits_dict = x_union.limits_dict
    i, *_ = limits_dict.keys()
    xi = x_union.function
    kwargs = i._assumptions.copy()
    if 'domain' in kwargs:
        del kwargs['domain']

    j = xi.generate_free_symbol(excludes=excludes, **kwargs)
    xj = xi.subs(i, j)

    i_domain = limits_dict[i] or i.domain

    limits = [(j, i_domain // {i})] + [*x_union.limits]
    return ForAll(Equality(xi & xj, xi.etype.emptySet).simplify(), *limits)


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    k = Symbol.k(integer=True, positive=True)
    
    j = Symbol.j(domain=Interval(0, k, integer=True) // {i})
    
    assert j <= k
    assert k >= j
    assert (j - k).is_nonpositive
    assert (k - j).is_nonnegative

    x = Symbol.x(shape=(k + 1,), etype=dtype.integer, finite=True)

    Eq << apply(Equality(abs(UNION[i:0:k](x[i])), Sum[i:0:k](abs(x[i]))))

    j = Eq[-1].variables[0]

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(sets.is_nonemptyset.imply.is_positive)

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(x[i], x[j])

    Eq << Eq[-2].this.function.apply(algebre.eq.gt.imply.lt.subs, Eq[-1])
    
    Eq.gt = Eq[0] - Eq[-1]

    Eq << Eq[0].lhs.arg.this.bisect({i, j})

    Eq.union_less_than = sets.imply.le.union_comprehension.apply(x[i], *Eq[-1].rhs.args[0].limits)

    Eq << sets.imply.le.union.apply(*Eq[-1].rhs.args)

    Eq << Eq.gt.this.function.apply(algebre.gt.le.imply.gt.subs, Eq[-1])
  
    Eq << Eq[-1].this().function.simplify()

    Eq << Eq[-1].this.function.apply(algebre.gt.le.imply.gt.subs, Eq.union_less_than)

    Eq << Eq[-1].this().function.lhs.simplify()


if __name__ == '__main__':
    prove(__file__)

