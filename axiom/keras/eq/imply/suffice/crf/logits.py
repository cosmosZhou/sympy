from util import *


@apply
def apply(given, G, x, s):
    t = s.definition.variable
    y = x.definition.variable.base
    return Suffice(t > 0, Equal(s[t], G[y[t], y[t - 1]] + s[t - 1] + x[t, y[t]]))


@prove
def prove(Eq):
    from axiom import algebra, sets

    #d is the number of output labels
    #oo is the length of the sequence
    d = Symbol.d(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(n, d), real=True, random=True, given=True)
    y = Symbol.y(shape=(n,), domain=Range(0, d), random=True, given=True)
    i = Symbol.i(integer=True)
    t = Symbol.t(domain=Range(0, n + 1))
    joint_probability_t = Probability(x[:t + 1], y[:t + 1])
    emission_probability = Probability(x[i] | y[i])
    transition_probability = Probability(y[i] | y[i - 1])
    given = Equal(joint_probability_t, Probability(x[0] | y[0]) * Probability(y[0]) * Product[i:1:t + 1](transition_probability * emission_probability))
    y = pspace(y).symbol
    G = Symbol.G(Lamda[y[i - 1], y[i]](-log(transition_probability)))
    s = Symbol.s(Lamda[t](-log(joint_probability_t)))
    x = Symbol.x(Lamda[y[i], i](-log(emission_probability)))
    Eq.given, Eq.s_definition, Eq.G_definition, Eq.x_definition, Eq.logits_recursion = apply(given, G, x, s)

    Eq << Eq.s_definition.this.rhs.subs(Eq.given)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.log.to.add)

    Eq << Eq[-1].subs(Eq.x_definition.subs(i, 0).reversed)

    Eq << Eq[-1].this.rhs.args[-1].args[1].apply(algebra.log.to.sum)

    Eq << Eq[-1].this.rhs.args[-1].args[1].expr.apply(algebra.log.to.add)

    Eq << Eq[-1].this.rhs.args[-1].args[1].apply(algebra.sum.to.add)

    Eq << Eq[-1].subs(Eq.x_definition.reversed).subs(Eq.G_definition.reversed)

    Eq << Eq[-1].this.rhs.args[-1].apply(algebra.sum.to.add.push_front)

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.args[1].apply(sets.notcontains.imply.notcontains.sub, 1)

    Eq << algebra.ou.imply.suffice.apply(Eq[-1], 1)

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.sub, Eq[-4])

    Eq << Eq[-1].this.rhs.rhs.simplify()

    Eq << Eq[-1].this.rhs.apply(algebra.eq.transposition, lhs=-1)

    Eq << Eq[-1].subs(t, t - 1)

    Eq << Eq[-1].this.args[1].apply(sets.notcontains.imply.notcontains.add, 1)

    Eq << algebra.ou.imply.suffice.apply(Eq[-1], 1)

    Eq << Eq[-1].this.lhs.apply(algebra.is_nonzero.given.is_positive)

    #reference: Neural Architectures for Named Entity Recognition.pdf


if __name__ == '__main__':
    run()
