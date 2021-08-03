from util import *


@apply
def apply(self):
    x, domain = self.of(Contains)
    assert domain in Interval(-S.Pi, S.Pi, left_open=True)
    return Equal(Arg(exp(S.ImaginaryUnit * x)), x)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True)
    Eq << apply(Contains(x, Interval(-S.Pi, S.Pi, left_open=True)))

    Eq << Eq[1].this.lhs.apply(algebra.arg_expi.to.add.ceiling)

    Eq << sets.contains.imply.contains.div.interval.apply(Eq[0], 2 * S.Pi)

    Eq << sets.contains.imply.contains.sub.apply(Eq[-1], S.One / 2)

    Eq << sets.contains.imply.eq.ceiling.apply(Eq[-1])

    Eq << Eq[2].subs(Eq[-1])

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
