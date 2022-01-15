from util import *


@apply
def apply(given, index=-1):
    eqs, *limits = given.of(Any[And])
    first = And(*eqs[:index])
    second = And(*eqs[index:])
    first = Any(first, *limits)
    second = Any(second, *limits)
    return first, second



@prove
def prove(Eq):
    from axiom import algebra

    x, c = Symbol(real=True)
    a, b = Symbol(real=True, given=True)
    f = Function(shape=(), real=True)
    Eq << apply(Any[x:a:b]((x <= c) & (f(x) >= 1)))

    Eq << algebra.any_et.imply.any.split.apply(Eq[0], index=0)
    Eq << algebra.any_et.imply.any.split.apply(Eq[0], index=1)




if __name__ == '__main__':
    run()
# created on 2018-08-23
