from util import *


@apply
def apply(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption, eq_s, eq_x, eq_G):
    from axiom.keras.eq.eq.eq.ne_zero.imply.eq.crf.markov import process_assumptions
    x, y = process_assumptions(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption)
    y = pspace(y).symbol
    x = pspace(x).symbol
    n, d = x.shape
    (s, t), (x_t1, y_t1) = eq_s.of(Equal[Indexed, -Log[Probability[And]]])
    (G, S[y[t]], S[y[t - 1]]), _ = eq_G.of(Equal[Indexed, -Log[Probability[Conditioned]]])
    return Infer(t > 0, Equal(s[t], G[y[t], y[t - 1]] + s[t - 1] + x[t, y[t]]))


@prove
def prove(Eq):
    from axiom import keras, algebra

    d, n = Symbol(domain=Range(2, oo))
    X = Symbol("x", shape=(n, d), real=True, random=True)
    Y = Symbol("y", shape=(n,), domain=Range(d), random=True)
    from axiom.keras.eq.eq.eq.ne_zero.imply.eq.crf.markov import markov_assumptions
    t = Symbol(integer=True)
    y = pspace(Y).symbol
    s = Symbol(shape=(n,), real=True)
    x = Symbol(shape=(n, d), real=True)
    G = Symbol(shape=(d, d), real=True)
    (*Eq[-4:], Eq.eq_s, Eq.eq_x, Eq.eq_G), Eq.infer = apply(*markov_assumptions(X, Y),
                                                                          Equal(s[t], -log(Probability(X[:t + 1], Y[:t + 1]))),
                                                                          Equal(x[t, y[t]], -log(Probability(X[t] | Y[t]))),
                                                                          Equal(G[y[t], y[t - 1]], -log(Probability(Y[t] | Y[t - 1]))))

    Eq << keras.eq.eq.eq.ne_zero.imply.eq.crf.markov.apply(*Eq[:4], t=t)

    Eq << Eq.eq_s.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.log.to.add)

    i = Symbol(integer=True)
    Eq << Eq[-1].subs(Eq.eq_x.subs(i, 0).reversed)

    Eq << Eq[-1].this.rhs.args[-1].args[1].apply(algebra.log.to.sum)

    Eq << Eq[-1].this.rhs.args[-1].args[1].expr.apply(algebra.log.to.add)

    Eq << Eq[-1].this.rhs.args[-1].args[1].apply(algebra.sum.to.add)

    Eq << algebra.eq.cond.imply.cond.subs.apply(-Eq.eq_x.reversed, Eq[-1])

    
    Eq << algebra.eq.cond.imply.cond.subs.apply(-Eq.eq_G.reversed, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-01-28
# updated on 2022-03-17
