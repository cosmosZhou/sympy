from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, geometry
from axiom.keras.layers.bert.position_representation.sinusoidal.definition import sinusoid_position_encoding

 
@apply
def apply(n, d):
    PE = sinusoid_position_encoding(n, d)
    j, i = PE.definition.variables
        
    k = Symbol.k(integer=True)
    
    PE_quote = sinusoid_position_encoding(n, d, inverse=True)
    
    (e0, c0), (e1, _) = PE[k, j].definition.args
    
    F = Symbol.F(definition=LAMBDA[j:d, k:n](Piecewise((cos(e0.arg), c0), (e1, True))))

    F_quote = Symbol("F'", definition=LAMBDA[j:d, k:n](Piecewise((e0, c0), (sin(e1.arg), True))))
    
    I = S.ImaginaryUnit
    z = Symbol.z(definition=F - I * F_quote)    
    
    Z = Symbol.Z(definition=PE * I - PE_quote)
    
    return Equality(Z[i + k], Z[i] * z[1] ** k)


@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True)
    d = Symbol("d_model", integer=True, positive=True, even=True)
    Eq << apply(n, d)
    
    PE_quote = Eq[0].lhs.base 
    PE = Eq[1].lhs.base
    
    i, j = Eq[0].lhs.indices
    k = Eq[3].lhs.indices[0]
    
    Eq.PE_definition = PE[i + k, j].this.definition
    
    Eq.PE_quote_definition = PE_quote[i + k, j].this.definition
    
    Eq << Eq.PE_definition.rhs.args[0].expr.this.arg.astype(Plus) 
    
    Eq << Eq.PE_definition.rhs.args[1].expr.this.arg.astype(Plus)
    
    Eq <<= geometry.plane.trigonometry.sine.principle.add.apply(*Eq[-2].rhs.arg.args), geometry.plane.trigonometry.cosine.principle.add.apply(*Eq[-1].rhs.arg.args)
 
    Eq <<= algebre.equal.equal.imply.equal.transit.apply(Eq[-4], Eq[-2]), algebre.equal.equal.imply.equal.transit.apply(Eq[-3], Eq[-1])
     
    Eq << Eq.PE_definition.this.rhs.args[0].expr.subs(Eq[-2])
     
    Eq.cossin = Eq[-1].this.rhs.args[1].expr.subs(Eq[-2])
     
    Eq << Eq[1] * Eq[3]
         
    Eq << Eq[-1].this.rhs.astype(Piecewise)
     
    Eq << Eq[0] * Eq[4]
         
    Eq << Eq[-1].this.rhs.astype(Piecewise)
     
    Eq << Eq[-1] + Eq[-3]
     
    Eq << Eq[-1].this.rhs.astype(Piecewise)
     
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq.cossin, Eq[-1])
     
    Eq << algebre.equal.imply.equal.lamda.apply(Eq[-1], (j, 0, d))
     
    Eq.PE_equality = Eq[-1].this.rhs.astype(Plus)
     
    Eq << Eq.PE_quote_definition.rhs.args[0].expr.this.arg.astype(Plus) 
     
    Eq << Eq.PE_quote_definition.rhs.args[1].expr.args[1].this.arg.astype(Plus)
     
    Eq <<= geometry.plane.trigonometry.cosine.principle.add.apply(*Eq[-2].rhs.arg.args), geometry.plane.trigonometry.sine.principle.add.apply(*Eq[-1].rhs.arg.args)
     
    Eq <<= algebre.equal.equal.imply.equal.transit.apply(Eq[-4], Eq[-2]), algebre.equal.equal.imply.equal.transit.apply(Eq[-3], Eq[-1])
     
    Eq << Eq.PE_quote_definition.this.rhs.args[0].expr.subs(Eq[-2])
     
    Eq.coscos = Eq[-1].this.rhs.args[1].expr.subs(Eq[-2])
     
    Eq << Eq[1] * Eq[4]
         
    Eq << Eq[-1].this.rhs.astype(Piecewise)
     
    Eq << Eq[0] * Eq[3]
     
    Eq << Eq[-1].this.rhs.astype(Piecewise)
     
    Eq << Eq[-1] - Eq[-3]
 
    Eq << Eq[-1].this.rhs.astype(Piecewise)
     
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq.coscos, Eq[-1])
     
    Eq << algebre.equal.imply.equal.lamda.apply(Eq[-1], (j, 0, d))
     
    Eq << Eq[-1].this.rhs.astype(Plus)
 
    I = S.ImaginaryUnit
    Eq << I * Eq.PE_equality - Eq[-1]
     
    Eq << Eq[-1].this.rhs.expand()
     
    Eq << Eq[-1].this.rhs.collect(PE[i])
    
    Eq.collect = Eq[-1].this.rhs.collect(PE_quote[i])
     
    F_quote = Eq[1].lhs.base
    F = Eq[3].lhs.base
     
    z = Eq[5].lhs
     
    Eq << z[k].this.definition
     
    Eq << Eq[-1] * I
     
    Eq << Eq[-1].this.rhs.expand()
     
    Eq << Eq.collect.subs(Eq[-1].reversed, Eq[-3].reversed)
     
    Eq << Eq[-1].this.rhs.collect(z[k])
     
    Z = Eq[2].lhs
    Eq << Z[i].this.definition
     
    Eq << Eq[-2].subs(Eq[-1].reversed)
     
    Eq << Z[k + i].this.definition 
     
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].subs(k, 1)
    
    Eq << algebre.equal.imply.equal.geometric_progression.apply(Eq[-1], n=i)
    
    Eq << Eq[-1].subs(i, i + k)
    
    Eq << Eq[-2] * z[1] ** k
    
    Eq << Eq[-1].this.rhs.powsimp()
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-3], Eq[-1])


if __name__ == '__main__':
    prove(__file__)
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
