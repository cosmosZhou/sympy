from sympy import *
from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling
from axiom import sets, algebra


@apply
def apply(n, k, s2=None, A=None):
    j = Symbol.j(domain=Interval(0, k, integer=True))
    if s2 is None: 
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        s2 = Symbol.s2(UNION[x[:k + 1]:Stirling.conditionset(n + 1, k + 1, x)](x[:k + 1].set_comprehension().set))

    e = Symbol.e(**s2.etype.dict)
    if A is None:
        x = s2.definition.variable.base
        i = Symbol.i(integer=True)
        s1_quote = Symbol("s'_1", Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol("x'", LAMBDA[i:k + 1](Piecewise(({n} | x[i], Equal(i, j)), (x[i], True))))
        A = Symbol.A(LAMBDA[j](UNION[x[:k + 1]:s1_quote]({x_quote.set_comprehension()})))        

    return Equal(conditionset(e, NotContains({n}, e), s2), UNION[j](A[j]))


@prove(surmountable=False)
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True, given=True)
    Eq << apply(n, k)

    s2_quote = Symbol.s_quote_2(conditionset(Eq[0].rhs.variable, Eq[0].rhs.limits[0][1]))
    Eq << s2_quote.this.definition
    
    Eq.s2_definition = imageset(Eq[0].rhs.variable, Eq[0].rhs.function.arg, s2_quote).this.subs(Eq[-1]).subs(Eq[0].reversed).reversed
    
    s1_quote = Eq[2].lhs 

    Eq << sets.imply.forall.conditionset.apply(s1_quote)

    i = Eq[1].lhs.indices[0]
    x_slice = Eq[-1].limits[0][0]
    x = x_slice.base

    Eq.x_abs_positive_s1, Eq.x_abs_sum_s1, Eq.x_union_s1 = algebra.forall_et.imply.forall.apply(Eq[-1])

    j = Symbol.j(domain=Interval(0, k, integer=True))

    x_quote = Eq[1].lhs.base

    Eq.x_quote_set_in_s2 = Subset(imageset(x_slice, UNION[i:k + 1](x_quote[i].set), s1_quote), Eq[0].lhs, plausible=True)

    Eq << sets.subset.given.forall_contains.apply(Eq.x_quote_set_in_s2)

    Eq << Eq[-1].subs(Eq.s2_definition)

    Eq << Eq[-1].this.function.apply(sets.contains.given.contains.split.imageset)
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq << Eq[-1].this.function.args[0].simplify()
    
    Eq << sets.eq.imply.eq.union_comprehension.apply(Eq[1], (i, 0, k + 1))

    Eq.x_quote_union = algebra.forall_eq.cond.imply.forall.subs.apply(Eq.x_union_s1, Eq[-1])

    Eq << Eq[1].apply(algebra.eq.imply.eq.abs)
    x_quote_abs = Eq[-1]
    
    Eq << Eq[-1].apply(algebra.eq.imply.eq.sum, (i, 0, k + 1))

    Eq << sets.imply.le.union.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << algebra.eq.le.imply.le.subs.apply(Eq[-2], Eq[-1])
    
    Eq << algebra.forall_eq.cond.imply.forall.subs.apply(Eq.x_abs_sum_s1, Eq[-1])

    Eq << Eq.x_quote_union.this.function.apply(algebra.eq.imply.eq.abs)    
        
    x_quote_union_abs = Eq[-1]

    u = Eq[-1].lhs.arg
    Eq << sets.imply.le.union_comprehension.apply(u.function, *u.limits)

    Eq << Eq[-2].this.function.apply(algebra.eq.le.imply.ge.subs, Eq[-1])
    
    Eq.SqueezeTheorem = Eq[-4] & Eq[-1]

    Eq << algebra.eq.imply.ou.two.apply(x_quote_abs)
    
    Eq << Eq[-1].subs(i, j)
    
    Eq << Eq[-2].apply(algebra.cond.imply.forall.restrict, (i, Unequal(i, j)))

    Eq << sets.imply.ge.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq.x_abs_positive_s1.limits_subs(i, j).this.function.apply(algebra.gt.ge.imply.gt.transit, Eq[-1])

    Eq.xj_is_positive = Eq[-1].subs(Eq[-4].reversed)

    Eq << algebra.forall.forall.imply.forall_et.limits_intersect.apply(Eq.x_abs_positive_s1, Eq[-3].reversed)
    
    Eq.xi_is_positive = Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.transit)

    Eq.xi_forall_is_positive = Eq.xi_is_positive.apply(algebra.forall.given.forall.limits.delete, index=0)
    
    Eq << Eq.xi_forall_is_positive.this.function.apply(algebra.cond.given.et.forall, cond=Equal(i, j))
    
    Eq << algebra.forall_et.given.forall.apply(Eq[-1])
    
    Eq << Eq[-1].apply(algebra.forall.given.forall_ou.limits.delete, simplify=None)
    
    Eq << Eq[-1].this.find(NotContains).apply(sets.notcontains.given.ou.split.complement, simplify=None)
    
    Eq << Eq[-1].this.find(Greater).apply(algebra.cond.given.ou.domain_defined, wrt=i, simplify=None)
    
    Eq << Eq.xi_is_positive.apply(algebra.forall.imply.forall_ou.limits.delete, simplify=None)
    
    Eq << Eq[-1].this.find(NotContains).apply(sets.notcontains.imply.ou.split.complement, simplify=None)
    
    Eq <<= Eq.x_quote_union & Eq.SqueezeTheorem & Eq.xi_forall_is_positive
     
    Eq.x_quote_definition = Eq[1].apply(algebra.eq.imply.eq.lamda, (i, 0, k + 1), simplify=False)
  
    Eq.subset_A = Subset(Eq[4].lhs, Eq[4].rhs, plausible=True)
    Eq.supset_A = Supset(Eq[4].lhs, Eq[3].lhs, plausible=True)

    Eq << Eq.supset_A.subs(Eq[3])
    
    Eq << sets.supset.given.forall_contains.apply(Eq[-1])
    
    Eq << Eq[-1].this.function.simplify()
      
    Eq << algebra.forall_et.given.forall.apply(Eq[-1])
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.exists_contains.split.union_comprehension)
    
    Eq << Eq.x_quote_definition[j]
    
    Eq << Eq[-2].reversed.this.function.apply(sets.eq.eq.imply.eq.intersect, Eq[-1])
    
    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(*Eq[-1].lhs.args)
    
    Eq << algebra.exists_eq.cond.imply.exists.subs.apply(Eq[-2], Eq[-1])
    
    Eq.set_size_inequality = Eq[-1].this.function.apply(algebra.eq.lt.imply.lt.subs, Less(Eq[-1].function.rhs, Eq[-1].function.rhs + 1, plausible=True))
    
    Eq << Eq.x_quote_union.this.function.lhs.bisect({i, j})
    
    Eq << sets.imply.le.union.apply(*Eq[-1].lhs.args)
    
    Eq << sets.imply.le.union_comprehension.apply(*Eq[-2].lhs.args[0].args)
    
    Eq << algebra.le.le.imply.le.subs.apply(Eq[-2], Eq[-1])
    
    Eq << algebra.cond.exists.imply.exists_et.apply(Eq[-1], Eq.set_size_inequality)
    
    Eq << Eq[-1].this.function.apply(algebra.lt.le.imply.lt.add)
    
    Eq << Eq[-1].this(var=Eq[-1].variables[0]).find(Sum).simplify()
    
    Eq << Eq[-1].this(var=Eq[-1].variables[0]).function.rhs.find(UNION).simplify()
    
    Eq << algebra.forall.exists.imply.exists_et.apply(x_quote_union_abs, Eq[-1])
    
    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs)
    
    Eq << algebra.forall.exists.imply.exists_et.apply(Eq.SqueezeTheorem, Eq[-1])    
    
    Eq << Eq.subset_A.subs(Eq[3])
    
    Eq << sets.subset.given.forall_contains.apply(Eq[-1])
    
    s2_hat_n = Symbol("\hat{s}_{2, n}", conditionset(*Eq[-1].limits[0]))

    Eq << sets.forall.given.forall.conditionset.split.baseset.apply(Eq[-1], simplify=False, s=s2_hat_n)

    Eq.s2_hat_n_assertion = Eq[-1].this.function.apply(sets.contains.given.exists_contains.split.union_comprehension)
    
    Eq << s2_hat_n.this.definition
    
    Eq << Eq[-1].this.rhs.apply(sets.conditionset.to.imageset)
    
    s2_quote_n = Symbol("s'_{2, n}", conditionset(Eq[-1].rhs.variable, Eq[-1].rhs.limits[0][1]))

    assert s2_quote_n in s2_quote
    assert Supset(s2_quote, s2_quote_n)

    Eq << s2_quote_n.this.definition
    
    Eq << imageset(Eq[-2].rhs.variable, Eq[-2].rhs.function.arg, s2_quote_n).this.subs(Eq[-1]).subs(Eq[-2].reversed).reversed
    
    Eq.s2_hat_n_hypothesis = Eq.s2_hat_n_assertion.this.limits[0].subs(Eq[-1])
    
    Eq << sets.imply.forall.conditionset.apply(s2_quote_n)
    
    Eq << Eq[-1].this.function.apply(sets.eq.eq.forall_is_positive.notcontains.imply.eq.stirling2, s1=s1_quote)
    
    Eq << algebra.forall_exists.imply.forall_exists.limits_swap.apply(Eq[-1])
    
    Eq << Eq.s2_hat_n_hypothesis.this.function.function.apply(sets.eq.given.eq.set_comprehension)
    
    Eq << Eq[-1].subs(Eq.x_quote_definition)
    
    Eq.supset_A = sets.supset.imply.supset.union_comprehension.lhs.apply(Eq.supset_A, (j,), simplify=False)
    
    Eq <<= Eq.supset_A & Eq.subset_A


if __name__ == '__main__':
    prove()

