from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


def index_function(n): 
    k = Symbol.k(integer=True)
    
    def index(x, a, *indices):
        (j,), *_ = indices
        return LAMBDA[k:n](KroneckerDelta(x[k], a[j])) @ LAMBDA[k:n](k)

    f = Function.index(nargs=(2,), shape=(), integer=True)
    f.eval = index
    return f


@apply
def apply(*given):
    forall_x, forall_p, equality = given
    assert forall_x.is_ForAll and forall_p.is_ForAll
    
    assert len(forall_x.limits) == 1
    x, S = forall_x.limits[0]
    
    assert forall_x.function.is_Equal
    x_set_comprehension, e = forall_x.function.args
    assert x_set_comprehension == x.set_comprehension()
    
    assert len(forall_p.limits) == 2
    (_x, _S), (p, P) = forall_p.limits
    assert x == _x and S == _S
    assert forall_p.function.is_Contains
    
    lamda, _S = forall_p.function.args
    assert S == _S
    assert lamda.is_LAMBDA
    
    n = x.shape[0]
    k = lamda.variable
    assert lamda == LAMBDA[k:n](x[p[k]])

    if P.is_set: 
        P = P.condition_set().condition
        
    assert p.shape[0] == n
    
    lhs, rhs = P.args
    assert rhs == Interval(0, n - 1, integer=True)    
    assert lhs == p.set_comprehension()
    
    assert equality.is_Equal
    
    assert equality.rhs == n
    assert equality.lhs.is_Abs
    assert equality.lhs.arg == e
     
    return Equal(abs(S), factorial(n))


@prove(surmountable=False)
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    S = Symbol.S(etype=dtype.integer * n)    
    
    x = Symbol.x(**S.element_symbol().type.dict)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    k = Symbol.k(integer=True)
    
    e = Symbol.e(etype=dtype.integer, given=True)
    
    p = Symbol.p(shape=(n,), integer=True, nonnegative=True)
    
    P = Symbol.P(conditionset(p[:n], Equal(p[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    
    Eq << apply(ForAll[x:S](Equal(x.set_comprehension(), e)),
                ForAll[x:S, p[:n]:P](Contains(LAMBDA[k:n](x[p[k]]), S)),
                Equal(abs(e), n))

    Eq << sets.eq.imply.exists_eq.apply(Eq[3])
    
    Eq << algebra.forall.exists.imply.exists_forall_et.apply(Eq[1], Eq[-1])
    
    Eq << Eq[-1].this.function.function.apply(algebra.eq.eq.imply.eq.transit)
    
    a, cond = Eq[-1].limits[0]
    index = index_function(n)
    
#     p= LAMBDA[j:n](index[j](x, a))
    
#     x[index[j](x, a)] = a[j]
    Eq << Exists[a:cond](ForAll[p:P](Contains(LAMBDA[k:n](a[p[k]]),
                                              S)))
    
    Eq << Exists[a:cond](ForAll[p:P](Equal(p, LAMBDA[j:n](index[j](LAMBDA[k:n](a[p[k]]),
                                                                      a)))))   
        
    Eq << Exists[a:cond](ForAll[x:S](Contains(LAMBDA[j:n](index[j](x,
                                                                   a)), P)))
    
    Eq << Exists[a:cond](ForAll[x:S](Equal(x,
                                              LAMBDA[k:n](a[LAMBDA[j:n](index[j](x, a))[k]]))))
    

if __name__ == '__main__':
    prove()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
