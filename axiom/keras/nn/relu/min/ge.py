from sympy import *
from axiom.utility import prove, apply
from axiom import algebre

import tensorflow as tf


@apply
def apply(x, y, z):
    return GreaterThan(tf.relu(x - y) + Min(y, z), Min(x, z))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    z = Symbol.z(real=True, given=True)
    Eq << apply(x, y, z)
    
    Eq << Eq[0].this.lhs.args[1].definition
    
    Eq << Eq[-1].this.lhs.args[0].astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.args[1].expr.astype(Min)
    
    Eq << Eq[-1].this.lhs.args[0].cond.reversed
    
    Eq << Eq[-1].bisect(x - y <= 0)
    
    Eq << algebre.et.given.cond.apply(Eq[-1])
    
    Eq <<= ~Eq[-2], ~Eq[-1]
    
    Eq <<= Eq[-2].apply(algebre.cond.cond.imply.et, swap=True), Eq[-1].apply(algebre.cond.cond.imply.et, invert=True, swap=True)
    
    Eq <<= Eq[-2].this.args[1] + y, Eq[-1].this.args[1] + z 
    
    Eq << Eq[-1].this.args[1].apply(algebre.gt.imply.ge.min, x)

    Eq << Eq[-2].this.args[1].apply(algebre.le.imply.le.min, z)


if __name__ == '__main__':
    prove(__file__)
