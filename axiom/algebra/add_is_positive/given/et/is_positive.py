from util import *


@apply
def apply(given, index=-1):
    args = given.of(Add > 0)
    first = args[:index]
    first = Add(*first)
    second = args[index:]
    second = Add(*second)
    return first > 0, second > 0


@prove
def prove(Eq):
    from axiom import algebra
    
    a, b = Symbol(real=True, given=True)
    Eq << apply(a + b > 0)
    
    Eq << algebra.is_positive.is_positive.imply.is_positive.add.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()