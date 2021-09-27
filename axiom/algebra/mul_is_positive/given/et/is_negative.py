from util import *


@apply
def apply(given, index=-1):
    args = given.of(Mul > 0)
    first = args[:index]
    first = Mul(*first)
    second = args[index:]
    second = Mul(*second)
    return first < 0, second < 0


@prove
def prove(Eq):
    from axiom import algebra
    a, b = Symbol(real=True, given=True)
    Eq << apply(a * b > 0)
    
    Eq << algebra.is_negative.is_negative.imply.is_positive.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()