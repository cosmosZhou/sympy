# coding=utf-8
from sympy import *
from axiom.utility import prove, apply
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes
from axiom import algebre, statistics


def assumptions():
    # d is the number of output labels    
    # oo is the length of the sequence
    d = Symbol.d(domain=Interval(2, oo, integer=True))
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    x = Symbol.x(shape=(n, d), real=True, random=True, given=True)
    y = Symbol.y(shape=(n,), domain=Interval(0, d - 1, integer=True), random=True, given=True)
    
    k = Symbol.k(domain=Interval(1, n - 1, integer=True))    
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


@apply(imply=True)
def apply(*given):
    x, y = process_assumptions(*given)
    n, _ = x.shape
    t = Symbol.t(integer=True, domain=Interval(0, n - 1, integer=True))    
    i = Symbol.i(integer=True)
    
    return Equality(P(x[:t + 1], y[:t + 1]),
                    P(x[0] | y[0]) * P(y[0]) * Product[i:1:t + 1](P(y[i] | y[i - 1]) * P(x[i] | y[i])))


@prove
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
    
    Eq.recursion = algebre.is_nonzero.equal.imply.equal.scalar.apply(Eq[0], Eq[-1])
    
    Eq << bayes.is_nonzero.is_nonzero.joint_slice.apply(Eq.xy_nonzero_assumption, [k, k])
    
    Eq << bayes.equal.equal.given_deletion.single_condition.apply(Eq.x_independence)
    
    Eq << bayes.equal.equal.conditional_joint_probability.joint_nonzero.apply(Eq[-1], Eq.xy_independence, Eq[-2])
    
    Eq << bayes.equal.equal.given_addition.joint_probability.apply(Eq[-1], Eq[0])
    
    Eq.recursion = Eq.recursion.subs(Eq[-1])
    
    Eq << statistics.bayes.theorem.apply(Eq.recursion.rhs, y[k])
    
    Eq.or_statement = algebre.forall.imply.ou.apply(Eq[-1])    
    
    Eq << Eq[2].subs(k, k + 1)
    
    Eq << algebre.ou.imply.forall.apply(Eq[-1], pivot=1)
    
    _, Eq.y_nonzero_assumption = bayes.is_nonzero.et.apply(Eq.xy_nonzero_assumption).split()
    Eq <<= Eq[-1] & Eq.y_nonzero_assumption
    
    Eq.y_joint_y_historic = Eq[-1].this.lhs.arg.bisect(Slice[-1:])
    
    Eq << bayes.is_nonzero.is_nonzero.conditioned.apply(Eq.y_joint_y_historic, y[:k])
    
    Eq << (Eq[-1] & Eq.or_statement).split()
    
    Eq.recursion = Eq.recursion.subs(Eq[-1])
    
    Eq.recursion = Eq.recursion.subs(Eq.y_independence)
    
    Eq << bayes.equal.equal.given_deletion.single_condition.apply(Eq.x_independence, wrt=y[:k])
    
    Eq << bayes.equal.equal.given_addition.joint_probability.apply(Eq.y_joint_y_historic, Eq[-1])
    
    Eq.recursion = Eq.recursion.subs(Eq[-1])
    
    Eq << algebre.equal.imply.equal.product.apply(Eq.recursion, (k, 1, k + 1))
    
    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variable, Eq.factorization.rhs.args[-1].variable)
    
    Eq << Eq[-1] * Eq[-1].lhs.args[0].base
    
    Eq.first = Eq.xy_joint_probability.subs(k, 1)
    
    Eq << Eq[-1].subs(Eq.first)
    
    t = Eq.factorization.rhs.args[-1].limits[0][2] - 1
    Eq << Eq[-1].subs(k, t)    
    
    Eq << algebre.ou.imply.forall.apply(Eq[-1], pivot=-1)
    
    Eq <<= Eq[-1] & Eq.first


# reference: Neural Architectures for Named Entity Recognition.pdf
if __name__ == '__main__':
    prove(__file__)
