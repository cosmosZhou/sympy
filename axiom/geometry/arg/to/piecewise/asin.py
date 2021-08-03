from util import *


@apply
def apply(self):
    x, y = self.of(Arg[Expr + ImaginaryUnit * Expr])
    r = sqrt(x ** 2 + y ** 2)
    return Equal(self, Piecewise((0, Equal(x, 0) & Equal(y, 0)), 
                                 (asin(y / r), (y >= 0) & (x >= 0)), 
                                 (S.Pi - asin(y / r), (y >= 0) & (x < 0)), 
                                 (-S.Pi - asin(y / r), (y < 0) & (x < 0)), 
                                 (-S.Pi + asin(y / r), True)))


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(Arg(x + y * S.ImaginaryUnit))

    Eq << Eq[0].this.lhs.apply(geometry.arg.to.piecewise.acos)

    

    

    

    

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()