from util import *


@apply
def apply(*given):
    from axiom.keras.layers.crf.markov import process_assumptions
    x, y = process_assumptions(*given)

    n, d = x.shape
    t = Symbol.t(domain=Range(0, n))
    i = Symbol.i(integer=True)

    joint_probability_t = Probability(x[:t + 1], y[:t + 1])
    joint_probability = Probability(x, y)
    emission_probability = Probability(x[i] | y[i])
    transition_probability = Probability(y[i] | y[i - 1])
    y = pspace(y).symbol

    G = Symbol.G(Lamda[y[i - 1], y[i]](-log(transition_probability)))
    assert G.shape == (d, d)
    s = Symbol.s(Lamda[t](-log(joint_probability_t)))
    assert s.shape == (n,)
    x = Symbol.x(Lamda[y[i], i](-log(emission_probability)))
    assert x.shape == (n, d)
    x_quote = Symbol.x_quote(Lamda[y[t], t](Minimize[y[:t]](s[t])))
    assert x_quote.shape == (n, d)

    assert x_quote.is_real
    return Equal(x_quote[t + 1], x[t + 1] + ReducedMin(x_quote[t] + G)), \
        Equal(Maximize[y](joint_probability), exp(-ReducedMin(x_quote[n - 1])))


@prove
def prove(Eq):
    from axiom import keras, algebra

    from axiom.keras.layers.crf.markov import assumptions
    Eq.s_definition, Eq.x_quote_definition, Eq.x_definition, Eq.G_definition, *given, Eq.recursion, Eq.joint_probability = apply(*assumptions())

    x_probability = given[-1].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
    s, t = Eq.s_definition.lhs.args
    Eq.x_quote_definition = Eq.x_quote_definition.apply(algebra.eq.imply.eq.lamda, (Eq.x_quote_definition.lhs.indices[-1],), simplify=False)

    Eq << keras.layers.crf.markov.apply(*given)

    Eq << keras.layers.crf.logits.apply(Eq.G_definition.lhs.base, Eq.x_definition.lhs.base, s, Eq[-1])

    Eq << Eq.x_quote_definition.subs(t, t + 1)

    y = Eq[-1].rhs.variable.base
    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[-1].this.rhs.function.simplify()

    Eq << Eq[-1].this.rhs.args[1].function.split(slice(-1))

    Eq << Eq[-1].this.rhs.args[1].function.apply(algebra.minimize.to.lamda)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.lamda.to.reducedMin)

    Eq << Eq[-1].subs(Eq.x_quote_definition.reversed)

    Eq << -Eq.s_definition.reversed

    Eq << Eq[-1].apply(algebra.eq.imply.eq.exp)

    Eq << algebra.eq.imply.eq.maximize.apply(Eq[-1], (y[:t + 1],))

    Eq << Eq[-1].this.rhs.apply(algebra.maximize.to.exp)

    Eq << algebra.eq.imply.eq.reducedMin.apply(Eq.x_quote_definition).this.rhs.simplify(wrt=t)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(t, n - 1)


if __name__ == '__main__':
    run()
