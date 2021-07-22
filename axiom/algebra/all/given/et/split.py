from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    from axiom.algebra.all.imply.et.split import split_all
    given = split_all(given, cond, wrt)
    return given.of(And)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(integer=True, shape=())
    d = Symbol.d(real=True, positive=True)
    Eq << apply(All[x:Interval(-d, d, left_open=True, right_open=True)](f(x) > 0), cond=x < 0)

    Eq <<= Eq[1] & Eq[2]

    


if __name__ == '__main__':
    run()