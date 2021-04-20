
from axiom.utility import prove, apply
from sympy.core.relational import Equal

from tensorflow.nn import softmax
from sympy import Symbol, log, exp, MAX, ReducedSum
from axiom import keras, algebra


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@apply
def apply(x):
    assert len(x.shape) == 1
    return Equal(log(softmax(x)), x - MAX(x) - log(ReducedSum(exp(x - MAX(x)))))

@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    
    x = Symbol.x(real=True, shape=(n,))
    Eq << apply(x)
    
    Eq << keras.nn.softmax.translation.apply(x, -MAX(x)).reversed
    
    Eq << Eq[-1].apply(algebra.eq.imply.eq.log)
    
    Eq << Eq[-1].this.rhs.arg.definition


if __name__ == '__main__':
    prove()
