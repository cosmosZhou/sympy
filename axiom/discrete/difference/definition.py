from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete


@apply
def apply(fx, x, n):
    k = fx.generate_free_symbol(x.free_symbols | n.free_symbols, integer=True)
    return Equal(Difference(fx, x, n),
                 Sum[k:0:n + 1]((-1) ** (n - k) * binomial(n, k) * fx.subs(x, x + k)))


@prove
def prove(Eq):
    f = Function('f', real=True)
    x = Symbol.x(real=True)
    fx = f(x)
    assert fx.is_real
    n = Symbol.n(integer=True, nonnegative=True, given=False)
    Eq << apply(fx, x, n)

    Eq.initial = Eq[0].subs(n, 0)
    
    Eq << Eq.initial.this.lhs.doit()
    
    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.bisect(Slice[:1])

    Eq << Eq[-1].this.lhs.expr.doit()

    Eq << Eq[-1].this.lhs.astype(Add)
    
    Eq << Eq[-1].this.rhs.bisect({0})
    
    Eq << Eq[-1].this.find(Sum).bisect({n + 1})
    
    Eq.hypothesis = algebra.cond.imply.cond.subs.apply(Eq[0], x, x + 1)
    
    Eq << Eq.hypothesis - Eq[0]

    i = Eq[-1].find(Sum).variable
    Eq << Eq[-1].this.find(Sum).limits_subs(i, i - 1)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.mul.to.sum)
    
    Eq << Eq[-1].this.find(Sum[2]).bisect({n + 1})
    
    Eq.bisect = Eq[-1].this.find(Sum).bisect({0})
    
    Eq << Add(*Eq.bisect.rhs.args[2:]).this.apply(algebra.add.to.sum)
    
    Eq << Eq[-1].this.rhs.function.collect(Mul(*Eq[-1].rhs.function.args[0].args[:-1]))
    
    Eq << discrete.combinatorics.binomial.Pascal.apply(n + 1, i)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq.bisect.subs(Eq[-1])
    
    Eq << Eq.induct.induct()
        
    Eq << algebra.eq.sufficient.imply.eq.induction.apply(Eq.initial, Eq[-1], n=n)
    


if __name__ == '__main__':
    prove()

