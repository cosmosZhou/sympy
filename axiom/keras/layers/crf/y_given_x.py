from util import *


@apply
def apply(*given):
    from axiom.keras.layers.crf.markov import process_assumptions
    x, y = process_assumptions(*given)
    n, d = x.shape

    t = Symbol.t(domain=Range(0, n))
    i = Symbol.i(integer=True)

    joint_probability = Probability(x[:t + 1], y[:t + 1])
    emission_probability = Probability(x[i] | y[i])
    transition_probability = Probability(y[i] | y[i - 1])
    y_given_x_probability = Probability(y | x)
    y = pspace(y).symbol

    G = Symbol.G(Lamda[y[i - 1], y[i]](-log(transition_probability)))
    assert G.shape == (d, d)

    s = Symbol.s(Lamda[t](-log(joint_probability)))
    assert s.shape == (n,)

    x = Symbol.x(Lamda[y[i], i](-log(emission_probability)))
    assert x.shape == (n, d)

    z = Symbol.z(Lamda[y[t], t](Sum[y[:t]](E ** -s[t])))
    assert z.shape == (n, d)

    x_quote = Symbol.x_quote(-Lamda[t](log(z[t])))
    assert x_quote.shape == (n, d)

    return Equal(x_quote[t + 1], -log(ReducedSum(exp(-x_quote[t] - G))) + x[t + 1]), \
        Equal(-log(y_given_x_probability), logsumexp(-x_quote[n - 1]) + s[n - 1])


@prove
def prove(Eq):
    from axiom import keras, algebra, discrete, stats

    from axiom.keras.layers.crf.markov import assumptions
    Eq.s_definition, Eq.z_definition, Eq.x_quote_definition, Eq.x_definition, Eq.G_definition, *given, Eq.recursion, Eq.y_given_x = apply(*assumptions())

    x_probability = given[-1].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
    s, t = Eq.s_definition.lhs.args
    Eq.z_definition = Eq.z_definition.apply(algebra.eq.imply.eq.lamda, (Eq.z_definition.lhs.indices[-1],), simplify=False)

    Eq << keras.layers.crf.markov.apply(*given)

    Eq << keras.layers.crf.logits.apply(Eq.G_definition.lhs.base, Eq.x_definition.lhs.base, s, Eq[-1])

    Eq << Eq.z_definition.subs(t, t + 1)

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[-1].this.find(Exp).apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.mul)

    Eq << Eq[-1].this.rhs.args[1].function.split(slice(-1))

    Eq << Eq[-1].this.rhs.args[1].function.apply(algebra.sum.to.reducedSum)

    Eq << Eq[-1].this.find(ReducedSum[~Lamda]).apply(algebra.lamda.to.mul)

    Eq << Eq[-1].this.find(Lamda).apply(discrete.lamda_reducedSum.to.matmul)

    Eq.z_recursion = Eq[-1].subs(Eq.z_definition.reversed)

    Eq << Eq.x_quote_definition.subs(t, t + 1)

    Eq << Eq[-1].this.rhs.subs(Eq.z_recursion)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.log.to.add)

    Eq.z_definition_by_x_quote = algebra.eq.imply.eq.exp.apply(-Eq.x_quote_definition.reversed) 

    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)

    Eq << Eq[-1].this.rhs.args[1].args[1].arg.apply(discrete.matmul.to.exp)

    Eq.xy_joint_nonzero = stats.is_nonzero.imply.is_nonzero.joint_slice.apply(given[-1], (slice(0, t + 1), slice(0, t + 1)))

    Eq << stats.is_nonzero.imply.et.apply(Eq.xy_joint_nonzero)

    y = Eq[-1].lhs.arg.lhs.base
    Eq << stats.is_nonzero.imply.eq.bayes.apply(Eq[-2], y[:t + 1])

    Eq << stats.sum.to.probability.apply(Sum[pspace(y[:t + 1]).symbol](Eq[-1].lhs))

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(algebra.eq.imply.ou.log)

    Eq << algebra.et.imply.et.apply(Eq[-1] & Eq.xy_joint_nonzero)

    Eq << Eq[-1].this.rhs.apply(algebra.log.to.add)

    Eq << algebra.eq.imply.eq.exp.apply(-Eq.s_definition.reversed)

    Eq.y_given_x_log = Eq[-2].subs(Eq[-1])

    Eq << Eq.z_definition.apply(algebra.eq.imply.eq.reducedSum)

    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)

    Eq << Eq.y_given_x_log.subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(t, n - 1)

    Eq << Eq.y_given_x.this.rhs.args[1].defun().reversed

    Eq << Eq[-1] + Eq[-2]

    #reference: Neural Architectures for Named Entity Recognition.pdf


if __name__ == '__main__':
    run()
