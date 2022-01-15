from util import *



@apply
def apply(given):
    p, q = given.of(Assuming)
    return p | q.invert()


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Assuming(x > y, f(x) > g(y)))

    Eq << Eq[0].reversed

    Eq << Eq[-1].apply(algebra.infer.imply.ou)


if __name__ == '__main__':
    run()
# created on 2018-09-18
