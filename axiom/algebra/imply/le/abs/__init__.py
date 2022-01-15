from util import *


@apply
def apply(x, negate=False):
    if negate:
        x = -x
    return LessEqual(x, abs(x))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    Eq << ~Eq[-1]
    
    Eq << GreaterEqual(abs(x), 0, plausible=True)
    
    Eq <<= Eq[-1] & Eq[-2]
    
    Eq << Eq[-1].this.apply(algebra.gt.ge.imply.gt.transit, ret=0, simplify=None)
    
    Eq << Eq[-1].this.args[0].apply(algebra.gt_zero.imply.eq.abs, simplify=None)
    
    Eq << Eq[-1].this.apply(algebra.gt.eq.imply.gt.transit)
    


if __name__ == '__main__':
    run()

from . import add
from . import substract
# created on 2018-06-29
# updated on 2022-01-04