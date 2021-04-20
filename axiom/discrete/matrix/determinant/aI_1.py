from sympy import *
from axiom.utility import prove, apply
from axiom import discrete, algebra


@apply
def apply(n, a):
    i = Symbol.i(integer=True)
    return Equal(Det(1 + a[:n] * Identity(n)), (1 + Sum[i:0:n](1 / a[i])) * Product[i:0:n](a[i]))


def column_transformation(*limits):
    n = limits[0][-1]
    (i, *_), (j, *_) = limits    
#     return Identity(n) + LAMBDA[j:n, i:n](Piecewise((0, i < n - 1), (KroneckerDelta(j, n - 1) - 1, True)))
#     return Identity(n) + LAMBDA[j:n, i:n](Piecewise((KroneckerDelta(j, n - 1) - 1, Equal(i, n - 1)), (0, True)))
    return Identity(n) + LAMBDA[j:n, i:n](KroneckerDelta(i, n - 1) * (KroneckerDelta(j, n - 1) - 1))
    return LAMBDA(Piecewise((KroneckerDelta(i, j), i < n - 1), (2 * KroneckerDelta(j, n - 1) - 1, True)), *limits)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=False)
    a = Symbol.a(shape=(oo,), complex=True, zero=False)
    Eq << apply(n, a)
    
    Eq.initial = Eq[-1].subs(n, 1)
    
    Eq << Eq.initial.this.lhs.doit()
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq.induction = Eq[0].subs(n, n + 1)
    
    Eq << discrete.matrix.determinant.expansion_by_minors.apply(Eq.induction.lhs.arg, i=n)

    Eq << Eq.induction.subs(Eq[-1])
    
    Eq << Eq[-1].this.lhs.bisect(Slice[-1:])
    
    Eq << Eq[-1].this.find(Sum)().find(Add).simplify()
    
    Eq << Eq[-1].this.find(LAMBDA)().function.simplify()
    
    Eq << Eq[-1].this.find(LAMBDA).apply(algebra.lamda.to.identity)
    
    Eq.deduct = (Eq[-1] - Eq[-1].lhs.args[0]).subs(Eq[0])
    
    Eq << Eq.deduct.find(Product).this.bisect(Slice[-1:])
    
    Eq << Eq.deduct.find(Mul, Sum).this.bisect(Slice[-1:])
    
    Eq << Eq.deduct.rhs.this.subs(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << algebra.et.given.cond.transit.apply(Eq.deduct & Eq[-1])
    
    Eq.deduction = Eq[-1].reversed
    
    D = Eq.deduction.lhs.function.args[1].arg
    
    i = Eq.deduction.lhs.variable.copy(domain=Interval(0, n - 1, integer=True))
    D = D._subs(Eq.deduction.lhs.variable, i)
    Eq << (D @ column_transformation(*D.limits)).this.expand()
    
    Eq << Eq[-1].this.find(Sum).bisect(Slice[-1:])
        
    Eq.bisect = Eq[-1].this.find(Add, LAMBDA)().find(Mul, KroneckerDelta).simplify()
    
    Eq << Eq.bisect.find(Sum).this().find(Add[2]).simplify()

    Eq << Eq.bisect.find(Sum[2]).this().find(Add[2]).simplify()
    
    Eq << Eq[-2] + Eq[-1]
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << Eq.bisect.this.rhs.subs(Eq[-1])
    
    Eq << Eq[-1].this.find(LAMBDA[~Add]).astype(Piecewise)

    Eq << Eq[-1].this.find(Add, Piecewise).apply(algebra.piecewise.swap.front)
    
    Eq << Eq[-1].this.find(Add, Piecewise).apply(algebra.piecewise.swap.back)
    
    Eq << Eq[-1].this.find(Add, Piecewise).apply(algebra.piecewise.invert)
    
    Eq << Eq[-1].this.find(Add, LAMBDA)().find(NotContains).simplify()
    
    Eq << Eq[-1].this.find(Add, Piecewise).apply(algebra.piecewise.subs, index=1)
    
    Eq << Eq[-1].this.find(Add, LAMBDA)().find(ExprCondPair)().expr.simplify()
    
    Eq.column_transformation = Eq[-1].this.find(ExprCondPair[3])().expr.simplify()    
   
    Eq << discrete.matrix.determinant.expansion_by_minors.apply(Eq.column_transformation.rhs, i=i).this.rhs.simplify(deep=True)
    
    Eq << Eq[-1].this.find(Mul, Piecewise, Add).astype(Piecewise)
    
    Eq << Eq[-1].this.find(Mul, Piecewise, Add).astype(Piecewise)

    Eq << Eq[-1].this.find(Mul, Det).doit()
    
    v = Eq[-1].find(Product).variable
    Eq << Eq[-1].this.find(Product).limits_subs(v, v - 1)
    
    k = Eq[-1].find(Product).variable
    Eq << Product[k:n](Eq[-1].find(Product).function).this.bisect({i})
    
    Eq << Eq[-2].subs((Eq[-1] / Eq[-1].rhs.args[0]).reversed)

    Eq << Eq.column_transformation.apply(algebra.eq.imply.eq.det)
    
    Eq << Eq[-1].subs(Eq[-2]).forall((i,))

    Eq << algebra.et.given.cond.subs.forall_eq.apply(Eq.deduction & Eq[-1])
    
    Eq << Eq[0].induct(reverse=True)
    
    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], n=n, start=1)

    
if __name__ == '__main__':
    prove()

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
