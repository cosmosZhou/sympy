from sympy.core.relational import Equality, Unequal, Equal

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol, Slice
from sympy.stats.symbolic_probability import Probability as P
from sympy.concrete.products import Product
from sympy import ArgMax
from axiom.statistics import bayes
from axiom import algebre, statistics
from sympy.logic.boolalg import Or

# given: x[t] | x[:t] = x[t], y[t] | y[:t] = y[t]
# imply: max[i]P(y[i] | x) = max[i](P(y[i]) * ∏[j:n](P(x[j] | y[i]))) 
@plausible
def apply(*given):
    x_equality, inequality = given
    
    assert inequality.is_Unequality
    xy_probability, zero = inequality.args
    assert xy_probability.is_Probability
    assert zero.is_zero
    xy_joint = xy_probability.arg
    
    assert x_equality.is_Equality
    
    x_t_given, x_t = x_equality.args
    
    assert x_t_given.is_Conditioned
    _x_t, x_t_historic = x_t_given.args
    
    assert x_t == _x_t
    
    x, t = x_t.args
    assert x_t_historic == x[:t].as_boolean()
    x_boolean, y_boolean = xy_joint._argset
    if x_boolean != x.as_boolean():
        x_boolean, y_boolean = y_boolean, x_boolean
    
    y = y_boolean.lhs        
    
    assert t.is_positive
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    return Equality(ArgMax[i](P(y[i] | x)), ArgMax[i](P(y[i]) * Product[j](P(x[j] | y[i]))))
    

@check
def prove(Eq):
    t = Symbol.t(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,), random=True)    
    y = Symbol.y(real=True, shape=(m,), random=True)
    
    Eq << apply(Equal(x[t] | x[:t], x[t]), Unequal(P(x, y), 0))
    
    i = Eq[-1].lhs.variable
    j = Eq[-1].rhs.function.args[-1].variable
    
    Eq << bayes.is_nonzero.et.apply(Eq[1]).split()
    Eq << bayes.corollary.apply(Eq[-2], var=y[i])
    
    Eq.y_given_x = algebre.is_nonzero.equality.imply.equality.scalar.apply(Eq[-1], Eq[-3]).reversed
    
    Eq << bayes.is_nonzero.is_nonzero.joint_slice.apply(Eq[1], [j, i])
    
    Eq << bayes.is_nonzero.et.apply(Eq[-1]).split()
    
    Eq << bayes.corollary.apply(Eq[-1], var=x)
    
    Eq.y_given_x = Eq.y_given_x.subs(Eq[-1])
    
    Eq << Eq.y_given_x.argmax((i,))
    
    Eq << bayes.is_nonzero.is_nonzero.joint_slice.apply(Eq[1], Slice[:t, i]) 
    
    Eq.xt_given_x_historic = bayes.equality.equality.given_addition.joint_probability.apply(Eq[0], Eq[-1])
    
    Eq.xt_given_yi_nonzero = bayes.is_nonzero.is_nonzero.conditioned.apply(Eq[-1], wrt=y[i])
    
    Eq << statistics.bayes.theorem.apply(P(x[:t + 1] | y[i]), x[:t])
    
    Eq << algebre.forall.imply.ou.apply(Eq[-1])
    
    Eq << (Eq[-1] & Eq.xt_given_yi_nonzero).split()
    
    Eq << Eq[-1].subs(Eq.xt_given_x_historic)
    
    Eq << algebre.is_nonzero.equality.imply.equality.scalar.apply(Eq[-1], Eq.xt_given_yi_nonzero)
    
    Eq << Eq[-1].product((t, 1, n - 1))
    
    t = Eq[-1].rhs.variable
    Eq << Eq[-1] / Eq[-1].lhs.args[-1]
    
    Eq << Eq[-1].this.rhs.astype(Product)
    
    Eq << Eq[-1].this.rhs.limits_subs(t, j)
    
    Eq << Eq[2].subs(Eq[-1].reversed)
    

if __name__ == '__main__':
    prove(__file__)
