
from axiom.utility import prove, apply
from sympy.core.relational import Equality

from tensorflow.nn import softmax
from sympy import Symbol

from sympy.core.mul import Times


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@apply
def apply(x, delta):
    assert len(x.shape) == 1
    assert not delta.shape

    return Equality(softmax(x + delta), softmax(x))




@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    
    x = Symbol.x(real=True, shape=(n,))
    delta = Symbol.delta(real=True)
    Eq << apply(x, delta)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.lhs.args[0].args[0].arg.astype(Times)
    
    Eq << Eq[-1].this.lhs.powsimp()
    
    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    prove(__file__)
