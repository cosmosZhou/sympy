from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(given, x=None, y=None):
    assert given.is_Equal
    abs_S, two = given.args
    assert abs_S.is_Abs
    assert two == 2
    S = abs_S.arg

    if x is None:
        x = S.generate_free_symbol(**S.etype.dict)
    if y is None:
        y = S.generate_free_symbol(excludes={x}, **S.etype.dict)
    return Exists[x: Unequal(x, y), y](Equal(S, {x, y}))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k)
    Eq << apply(Equal(abs(S), 2))
    
    Eq << algebra.eq.imply.ge.apply(Eq[0])
    Eq << sets.ge.imply.exists_ne.apply(Eq[-1])
    
    Eq << sets.exists.imply.exists.limits.swap.apply(Eq[-1], simplify=False)
        
    Eq.S_supset = Eq[-1].this.function.apply(sets.contains.contains.imply.subset, simplify=False)
    
    ab = Eq.S_supset.lhs
    
    Eq << Eq.S_supset.this.function.apply(sets.subset.imply.et.union)
    
    Eq << algebra.exists_et.imply.exists.limits_absorb.apply(Eq[-1], index=1)

    Eq << sets.imply.eq.principle.addition.apply(S, ab)    
    
    Eq << algebra.exists_eq.cond.imply.exists.subs.apply(Eq[-2], Eq[-1])
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-1].this.function - 2
    
    Eq << Eq[-1].this.function.apply(algebra.is_zero.imply.eq)
    
    Eq << Exists(Unequal(Eq[-1].rhs, 0), *Eq.S_supset.limits, plausible=True)
    
    Eq << Eq[-1].this.function.apply(algebra.is_nonzero.imply.eq.kronecker_delta)
    
    Eq << algebra.exists.imply.exists_et.multiple_variables.apply(Eq[-1])
    
    Eq << ~Eq[-2]
    
    Eq << algebra.forall.exists.imply.exists_et.apply(Eq[-1], Eq[-4])
    
    Eq << Eq[-1].this.function.apply(algebra.eq.eq.imply.eq.transit)
    
    Eq << Eq[-1].this.function.apply(sets.is_zero.imply.subset)
    
    Eq << algebra.exists.imply.exists_et.multiple_variables.apply(Eq[-1])
    
    Eq << algebra.exists_et.imply.exists.limits_absorb.apply(Eq[-1], index=1)
    
    Eq << Eq[-1].this.function.apply(sets.subset.subset.imply.eq.squeeze)
    

if __name__ == '__main__':
    prove()

