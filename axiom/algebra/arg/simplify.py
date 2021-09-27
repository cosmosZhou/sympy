from util import *


@apply
def apply(self):
    z = self.of(Arg[Exp[Arg * S.ImaginaryUnit]])    
    return Equal(self, Arg(z))


@prove
def prove(Eq):
    from axiom import algebra

    z = Symbol(complex=True)
    Eq << apply(Arg(exp(S.ImaginaryUnit * Arg(z))))

    Eq << Eq[0].this.lhs.apply(algebra.arg_expi.to.add.ceiling)

    Eq << Eq[-1].this.find(Ceiling).apply(algebra.ceiling.to.zero.arg)

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()