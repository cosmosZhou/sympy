from sympy import *
from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling
from axiom import sets, algebra


@apply
def apply(n, k, s0=None, B=None):
    
    if s0 is None: 
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        s0 = Symbol.s0(UNION[x[:k]:Stirling.conditionset(n, k, x)](x[:k].set_comprehension().set))
    if B is None:
        e = Symbol.e(**s0.etype.dict)
        assert e.is_extended_real
        B = Symbol.B(UNION[e:s0]({e | {n.set}}))
        
        assert B.definition.variable.is_extended_real        
    return Equal(abs(s0), abs(B))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True, given=True)
    n = Symbol.n(integer=True, positive=True, given=True)
    Eq << apply(n, k)

    s0 = Eq[0].lhs
    
    s0_quote = Symbol.s_quote_0(conditionset(Eq[0].rhs.variable, Eq[0].rhs.limits[0][1]))

    Eq << s0_quote.this.definition
    Eq.s0_definition = imageset(Eq[0].rhs.variable, Eq[0].rhs.function.arg, s0_quote).this.subs(Eq[-1]).subs(Eq[0].reversed).reversed

    e = Symbol.e(etype=dtype.integer.set)
    Eq << sets.imply.forall.baseset.apply(s0_quote)

    * _, Eq.x_union_s0 = algebra.forall_et.imply.forall.apply(Eq[-1])

    i = Symbol.i(integer=True)
    x = Eq[0].rhs.variable.base

    j = Symbol.j(domain=[0, k], integer=True)

    B = Eq[1].lhs
    Eq.plausible_notcontains = ForAll(NotContains({n}, e), (e, s0), plausible=True)

    Eq << Eq.plausible_notcontains.this.limits[0][1].subs(Eq.s0_definition)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.function.apply(sets.contains.imply.exists_contains.st.union_comprehension)
    
    Eq << algebra.forall.exists.imply.exists_et.apply(Eq.x_union_s0, Eq[-1].reversed, simplify=None)
    
    Eq << Eq[-1].this.function.apply(sets.eq.eq.imply.eq.union)
    
    Eq << Eq[-1].this().function.lhs.simplify()
    
    Eq << algebra.forall_eq.exists.imply.exists.subs.apply(Eq.x_union_s0, Eq[-1])

    Eq << Eq.plausible_notcontains.this.function.apply(sets.notcontains.imply.is_emptyset.intersection)

    Eq.forall_s0_equality = Eq[-1].this.function.apply(sets.is_emptyset.imply.eq.complement)

    x_hat = Symbol(r"\hat{x}", LAMBDA[i](Piecewise((x[i] - {n} , Equal(i, j)), (x[i], True))))

    Eq.x_hat_definition = x_hat.equality_defined()

    Eq << algebra.eq.imply.ou.st.piecewise.apply(Eq.x_hat_definition)
    
    Eq << Eq[-1].forall((i, Unequal(i, j)))
        
    Eq.B_assertion = sets.imply.forall_exists_eq.split.imageset.apply(B)

    Eq << Eq.B_assertion.this.function.function.apply(sets.eq.imply.eq.complement, {n.set})

    Eq << algebra.cond.forall.imply.forall_et.apply(Eq.forall_s0_equality, Eq[-1], simplify=None)
    
    Eq << Eq[-1].this.function.apply(algebra.forall.exists.imply.exists_et)
    
    Eq.forall_B_contains = Eq[-1].this.function.function.apply(algebra.eq.eq.imply.eq.subs, swap=True).limits_subs(Eq[-1].variable, Eq.forall_s0_equality.variable)

    Eq.forall_s0_contains = sets.imply.forall_contains.split.imageset.apply(B)
    
    Eq << Eq.B_assertion.this.function.function.apply(sets.eq.imply.eq.intersect, {n.set})
    
    Eq << Eq[-1].limits_subs(Eq.B_assertion.variable, Eq.B_assertion.function.variable)
    
    Eq.forall_B_equality = Eq[-1].this.function.apply(sets.eq.imply.eq.union, Eq[-1].variable)

    Eq << sets.forall_contains.forall_contains.forall_eq.forall_eq.imply.eq.apply(Eq.forall_s0_contains,
                                                                                  Eq.forall_B_contains,
                                                                                  Eq.forall_s0_equality,
                                                                                  Eq.forall_B_equality)


if __name__ == '__main__':    
    prove()

