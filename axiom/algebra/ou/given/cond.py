from util import *
import axiom



@apply
def apply(imply, index=None):
    eqs = imply.of(Or)
    if index is None:
        return eqs
    return eqs[index]


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    f = Function.f(real=True, given=True)

    Eq << apply((f(y) > 0) | (f(x) > 0), index=0)

    Eq << ~Eq[0]

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=0)

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

