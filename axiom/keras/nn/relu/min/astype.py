
from axiom.utility import prove, apply
from sympy.core.relational import Equality

from tensorflow.nn import softmax
from sympy import Symbol, log, exp
from sympy import Max, Min
from sympy.concrete.summations import Sum
from axiom import keras, algebre

import tensorflow as tf


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@apply(imply=True)
def apply(x, y):
    return Equality(y - tf.relu(-x + y), Min(x, y))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(x, y)
    
    Eq << Eq[0].this.lhs.args[1].args[1].definition
    
    Eq << Eq[-1].this.lhs.args[1].astype(Min)
    
    Eq << Eq[-1].this.lhs.astype(Min)


if __name__ == '__main__':
    prove(__file__)
