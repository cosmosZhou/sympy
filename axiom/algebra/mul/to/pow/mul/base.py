from util import *

def determine_exp(args):
    exponent = set()
    for arg in args:
        if arg.is_Pow:
            exponent.add(arg.exp)
            if len(exponent) > 1:
                return
            
    [exponent] = exponent
    return exponent
    
@apply
def apply(self):
    args = self.of(Mul)
    exponent = determine_exp(args)
    base = []
    unrealCount = 0
    
    for arg in args:
        if arg.is_Pow:
            b, e = arg.args
            if not b.is_extended_real:
                unrealCount += 1
        else:
            if arg > 0:             
                if arg.is_Rational:
                    b = arg ** (1 / exponent)
                    assert b.is_Rational
            else:
                return
                
        base.append(b)
    assert unrealCount < 2

    return Equal(self, Mul(*base) ** exponent, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    t = Symbol(integer=True)
    Eq << apply(x ** t * y ** t)

    Eq << Eq[-1].this.rhs.apply(algebra.pow.to.mul.split.base)


if __name__ == '__main__':
    run()

# created on 2018-11-13
# updated on 2018-11-13
