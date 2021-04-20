
from axiom.utility import prove, apply
from sympy.core.relational import Equal

from sympy import Symbol
from sympy import Max, Min

import tensorflow as tf


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@apply
def apply(x, y):
    return Equal(tf.relu(x - y) + y, Max(x, y))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(x, y)
    
    Eq << Eq[0].this.lhs.args[1].definition
    
    Eq << Eq[-1].this.lhs.astype(Max)


if __name__ == '__main__':
    prove()
