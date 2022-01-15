from util import *


@apply
def apply(el):
    t, (S[0], n) = el.of(Element[Range])
    j = Symbol(integer=True)
    t = Lamda[j:n](KroneckerDelta(j, t))

    assert n >= 2

    x = Symbol(shape=(n,), real=True)
    y = softmax(x)

    return Equal(Derivative(crossentropy(t, y), x), y - t)


@prove
def prove(Eq):
    from axiom import algebra, keras

    n = Symbol(domain=Range(2, oo))
    t = Symbol(integer=True)
    Eq << apply(Element(t, Range(n)))

    t = Symbol(Eq[1].find(Lamda))
    Eq << t.this.definition

    Eq << algebra.eq.imply.eq.reducedSum.apply(Eq[-1])

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.reducedSum.to.sum)

    Eq << keras.eq.imply.eq.crossentropy.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].this.definition)



if __name__ == '__main__':
    run()
# created on 2021-12-06
