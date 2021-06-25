from util import *



@apply
def apply(self, evaluate=False):
    from axiom.algebra.mul.to.min import extract
    rhs = extract(Max, self)
    
    return Equal(self, rhs, evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra

    t = Symbol.t(real=True, positive=True)
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(t * Max(x, y))
    Eq << Eq[0].this.rhs.apply(algebra.max.to.mul)


if __name__ == '__main__':
    run()