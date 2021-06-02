from util import *



@apply
def apply(x, y, z):
    return GreaterEqual(relu(x - y) + Min(y, z), Min(x, z))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    z = Symbol.z(real=True, given=True)
    Eq << apply(x, y, z)

    Eq << Eq[0].this.lhs.args[1].defun()

    Eq << Eq[-1].this.lhs.args[0].astype(Piecewise)

    Eq << Eq[-1].this.lhs.astype(Piecewise)

    Eq << Eq[-1].this.lhs.args[1].expr.astype(Min)

    Eq << Eq[-1].this.lhs.args[0].cond.reversed

    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=x - y <= 0)

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(algebra.cond.cond.imply.et, swap=True), Eq[-1].apply(algebra.cond.cond.imply.et, invert=True, swap=True)

    Eq <<= Eq[-2].this.args[1] + y, Eq[-1].this.args[1] + z

    Eq << Eq[-1].this.args[1].apply(algebra.gt.imply.ge.min, x)

    Eq << Eq[-2].this.args[1].apply(algebra.le.imply.le.min, z)


if __name__ == '__main__':
    run()
