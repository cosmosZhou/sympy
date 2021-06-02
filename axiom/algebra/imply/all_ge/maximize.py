from util import *



@apply
def apply(function, *limits): 
    return ForAll(GreaterEqual(MAX(function, *limits), function), *limits)


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    Eq << apply(f(x), (x, 0, oo))


if __name__ == '__main__':
    run()

