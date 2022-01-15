from util import *


@apply
def apply(x, y, z):
    return GreaterEqual(relu(x - y) + Min(y, z), Min(x, z))


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x, y, z)

    Eq << Eq[0].this.find(relu).defun()

    
    Eq << Eq[-1].this.lhs.args[0].apply(algebra.max.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.lhs.args[1].expr.apply(algebra.add.to.min)

    Eq << Eq[-1].this.lhs.args[0].cond.reversed

    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=x - y <= 0)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(algebra.cond.cond.imply.cond.subs, swap=True, ret=1), Eq[-1].apply(algebra.cond.cond.imply.cond.subs, invert=True, swap=True, ret=1)

    Eq <<= Eq[-2].this.args[1] + y, Eq[-1].this.args[1] + z

    Eq << Eq[-1].this.args[1].apply(algebra.gt.imply.ge.min, x)

    Eq << Eq[-2].this.args[1].apply(algebra.le.imply.le.min, z)

    
    


if __name__ == '__main__':
    run()
# created on 2020-12-27
# updated on 2022-01-08