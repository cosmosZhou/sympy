
from axiom.utility import prove, apply
from sympy.core.relational import Equal

from tensorflow.nn import softmax
from sympy import Symbol

from sympy.core.mul import Mul


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@apply
def apply(x, delta):
    assert len(x.shape) == 1
    assert not delta.shape

    return Equal(softmax(x + delta), softmax(x))




@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    
    x = Symbol.x(real=True, shape=(n,))
    delta = Symbol.delta(real=True)
    Eq << apply(x, delta)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.lhs.args[0].args[0].arg.astype(Mul)
    
    Eq << Eq[-1].this.lhs.powsimp()
    
    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    prove()
