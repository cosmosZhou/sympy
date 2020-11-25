# coding=utf-8
from axiom.utility import plausible
from sympy.core.relational import Equality, Unequal

from sympy import Symbol, Slice
from sympy.concrete.products import Product
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes
from sympy.core.numbers import oo
from axiom import algebre, sets, statistics
from sympy.logic.boolalg import Or


def assumptions():
    # d is the number of output labels    
    # oo is the length of the sequence
    d = Symbol.d(integer=True, domain=[2, oo])
    n = Symbol.n(integer=True, domain=[2, oo])
    x = Symbol.x(shape=(n, d), real=True, random=True, given=True)
    y = Symbol.y(shape=(n,), integer=True, domain=[0, d - 1], random=True, given=True)
    
    k = Symbol.k(integer=True, domain=[1, n - 1])    
    return Equality(x[k] | x[:k].as_boolean() & y[:k].as_boolean(), x[k]), Equality(y[k] | y[:k], y[k] | y[k - 1]), Equality(y[k] | x[:k], y[k]), Unequal(P(x, y), 0)


def process_assumptions(*given):
    x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption = given
    assert xy_nonzero_assumption.is_Unequality
    assert xy_nonzero_assumption.rhs.is_zero
    
    x = x_independence_assumption.rhs.base
    y = y_independence_assumption.lhs.lhs.base     
    assert y_independence_assumption.lhs.lhs == y_independence_assumption.rhs.lhs    
    
    assert xy_nonzero_assumption.lhs == P(x, y)
    
    assert xy_independence_assumption.rhs.base == y
    return x, y


@plausible
def apply(*given):
    x, y = process_assumptions(*given)
    n, _ = x.shape
    t = Symbol.t(integer=True, domain=[0, n - 1])    
    i = Symbol.i(integer=True)
    
    return Equality(P(x[:t + 1], y[:t + 1]),
                    P(x[0] | y[0]) * P(y[0]) * Product[i:1:t](P(y[i] | y[i - 1]) * P(x[i] | y[i])),
                    given=given)


from axiom.utility import check


@check
def prove(Eq):
    
    Eq.x_independence, Eq.y_independence, Eq.xy_independence, Eq.xy_nonzero_assumption, Eq.factorization = apply(*assumptions())
    
    y, k = Eq.y_independence.rhs.lhs.args
    
    Eq << Eq.x_independence.domain_definition()
    
    Eq << bayes.is_nonzero.et.apply(Eq[-1]).split()
    Eq << bayes.is_nonzero.is_nonzero.conditioned.apply(Eq[-3], y[:k])
    
    Eq << bayes.corollary.apply(Eq[-2], var=Eq[0].lhs.subs(k, k + 1))   
    
    Eq << bayes.corollary.apply(Eq[-2], var=Eq[-1].rhs.args[0])
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq.xy_joint_probability = bayes.corollary.apply(Eq[2], var=Eq[0].lhs)
    
    Eq << Eq[-1].subs(Eq.xy_joint_probability.reversed)
    
    Eq.recursion = algebre.is_nonzero.equality.imply.equality.apply(Eq[0], Eq[-1])
    
    Eq << bayes.is_nonzero.is_nonzero.joint_slice.apply(Eq.xy_nonzero_assumption, [k, k])
    
    Eq << bayes.equality.equality.given_deletion.single_condition.apply(Eq.x_independence)
    
    Eq << bayes.equality.equality.conditional_joint_probability.joint_nonzero.apply(Eq[-1], Eq.xy_independence, Eq[-2])
    
    Eq << bayes.equality.equality.given_addition.joint_probability.apply(Eq[-1], Eq[0])
    
    Eq.recursion = Eq.recursion.subs(Eq[-1])
    
    Eq.or_statement = statistics.bayes.theorem.apply(Eq.recursion.rhs, y[k]).astype(Or)
    
    Eq << Eq[2].subs(k, k + 1)
    
    Eq << sets.ou.imply.forall.apply(Eq[-1], wrt=k)
    
    _, Eq.y_nonzero_assumption = bayes.is_nonzero.et.apply(Eq.xy_nonzero_assumption).split()
    Eq <<= Eq[-1] & Eq.y_nonzero_assumption
    
    Eq.y_joint_y_historic = Eq[-1].this.lhs.arg.bisect(Slice[-1:])
    
    Eq << bayes.is_nonzero.is_nonzero.conditioned.apply(Eq.y_joint_y_historic, y[:k])
    
    Eq << (Eq[-1] & Eq.or_statement).split()
    
    Eq.recursion = Eq.recursion.subs(Eq[-1])
    
    Eq.recursion = Eq.recursion.subs(Eq.y_independence)
    
    Eq << bayes.equality.equality.given_deletion.single_condition.apply(Eq.x_independence, wrt=y[:k])
    
    Eq << bayes.equality.equality.given_addition.joint_probability.apply(Eq.y_joint_y_historic, Eq[-1])
    
    Eq.recursion = Eq.recursion.subs(Eq[-1])
    
    Eq << Eq.recursion.product((k, 1, k))
    
    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variable, Eq.factorization.rhs.args[-1].variable)
    
    Eq << Eq[-1] * Eq[-1].lhs.args[0].base
    
    Eq.first = Eq.xy_joint_probability.subs(k, 1)
    
    Eq << Eq[-1].subs(Eq.first)
    
    t = Eq.factorization.rhs.args[-1].limits[0][2]
    Eq << Eq[-1].subs(k, t)    
    
    Eq << sets.ou.imply.forall.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq.first


# reference: Neural Architectures for Named Entity Recognition.pdf
if __name__ == '__main__':
    prove(__file__)
