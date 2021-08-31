from util import *


@apply
def apply(self):
    x, domain = self.of(Element)
    assert domain in Interval(-S.Pi, S.Pi, left_open=True)
    return Equal(Arg(exp(S.ImaginaryUnit * x)), x)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(-S.Pi, S.Pi, left_open=True)))

    Eq << Eq[1].this.lhs.apply(algebra.arg_expi.to.add.ceiling)

    Eq << sets.el.imply.el.div.interval.apply(Eq[0], 2 * S.Pi)

    Eq << sets.el.imply.el.sub.apply(Eq[-1], S.One / 2)

    Eq << sets.el.imply.eq.ceiling.apply(Eq[-1])

    Eq << Eq[2].subs(Eq[-1])

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
