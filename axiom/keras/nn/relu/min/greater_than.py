
from axiom.utility import prove, apply
from sympy.core.relational import GreaterThan

from sympy import Symbol
from sympy import Min
from axiom import algebre

import tensorflow as tf
from sympy.functions.elementary.piecewise import Piecewise


@apply(imply=True)
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
    
    Eq << Eq[-1].bisect(x - y <= 0).split()
    
    Eq <<= ~Eq[-2], ~Eq[-1]
    
    Eq <<= Eq[-2].apply(algebre.condition.condition.imply.et, invert=True, swap=True), Eq[-1].apply(algebre.condition.condition.imply.et, swap=True)
    
    Eq <<= Eq[-2].this.args[1] + z, Eq[-1].this.args[1] + y
    
    Eq << Eq[-2].this.args[1].apply(algebre.strict_greater_than.imply.greater_than.min, x)

    Eq << Eq[-1].this.args[1].apply(algebre.less_than.imply.less_than.min, z)


if __name__ == '__main__':
    prove(__file__)
