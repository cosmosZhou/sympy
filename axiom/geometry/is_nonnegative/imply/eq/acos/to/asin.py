from util import *


@apply
def apply(is_nonnegative):
    x = is_nonnegative.of(Expr >= 0)    
    return Equal(acos(x), asin(sqrt(1 - x ** 2)))


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    theta = Symbol(acos(x))
    Eq << theta.this.definition

    Eq << geometry.square_cos.to.add.square_sin.apply(cos(theta) ** 2)

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()