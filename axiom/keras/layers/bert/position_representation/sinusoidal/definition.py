from sympy import LAMBDA, sin, cos, log, exp, dtype
from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol
from sympy.functions.elementary.piecewise import Piecewise

from axiom import algebre


def sinusoid_position_encoding(n, d, b=10000, inverse=False):
    j = Symbol.j(integer=True)
    i = Symbol.i(integer=True)

    if inverse:
        return Symbol("PE'", LAMBDA[j:d, i:n](Piecewise((cos(i / b ** (j / d)), (-1) ** j > 0),
                                              (-sin(i / b ** ((j - 1) / d)), True))))
    else:
        return Symbol.PE(LAMBDA[j:d, i:n](Piecewise((sin(i / b ** (j / d)), (-1) ** j > 0),
                                              (cos(i / b ** ((j - 1) / d)), True))))


@apply
def apply(n, d):
    PE = sinusoid_position_encoding(n, d)
    j, i = PE.definition.variables
    
    half_dim = Symbol("d'", d / 2)
    assert half_dim.is_integer
    assert half_dim.type in dtype.integer
        
#     emb = log(10000) / (half_dim - 1)
    emb = log(10000) / half_dim
    
    indices = LAMBDA[j:half_dim](j)
    
    emb = exp(indices * -emb)
    
    pos = LAMBDA[i:n](i)
    
    emb = LAMBDA[j:half_dim, i:n](pos[i] * emb[j])
    SIN = sin(emb)
    COS = cos(emb)
    emb = LAMBDA[j:d, i:n](Piecewise((SIN[i, j / 2], (-1) ** j > 0), (COS[i, (j - 1) / 2], True)))
        
    return Equality(PE, emb)


@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True)
    d = Symbol("d_model", integer=True, positive=True, even=True)
    Eq << apply(n, d)
    
    PE = Symbol("PE'", Eq[2].rhs)
    j, i = Eq[2].rhs.variables
    
    Eq << PE[i, j].this.definition
    
    Eq << Eq[-1].rhs.args[0].expr.arg.this.args[1].arg.args[1].base.definition
    
    Eq << Eq[-1].this.rhs.args[1].arg.astype(log)
    
    Eq << Eq[-3].this.rhs.subs(Eq[-1])
    
    Eq << Eq[-1].rhs.args[1].expr.arg.this.args[1].arg.args[1].base.definition
    
    Eq << Eq[-1].this.rhs.args[1].arg.astype(log)
    
    Eq << Eq[-1].this.rhs.args[0].args[1].expand()
    
    Eq << Eq[-4].this.rhs.subs(Eq[-1])
    
    Eq << algebre.equal.imply.equal.lamda.apply(Eq[-1], (j, 0, d), (i, 0, n))
    
    Eq << Eq[0].this.rhs.args[1].expr.arg.args[0].args[1].expand()
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << PE.this.definition
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    prove(__file__)
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
