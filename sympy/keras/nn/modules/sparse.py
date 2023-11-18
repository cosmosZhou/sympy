from .module import Module

from sympy.core.symbol import Symbol
from sympy.concrete.expr_with_limits import Lamda
from sympy.tensor.tensor import TensorUnequal
    
    
class Embedding(Module):

    def __init__(self, input_dim, output_dim):
        super().__init__()
        self.W = Symbol(real=True, shape=(input_dim, output_dim))
        
    def forward(self, indices, **kwargs):
        vars, limits = indices.variables_with_limits()
        embedding = Lamda(self.W[indices[tuple(vars)]], *limits)
        
        mask = kwargs.get('mask', None)
        if mask is None:
            return embedding
        
        mask = TensorUnequal(indices, 0) if mask else None
        
        from sympy.core.singleton import S
        S[self.W], S[indices] = embedding.of_embedding()
        return embedding, mask
        
