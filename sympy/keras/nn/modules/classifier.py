from ... import nn
from .module import Module

from sympy.core.symbol import Symbol
from sympy.functions.elementary.hyperbolic import Tanh
from sympy.functions.elementary.exponential import Log
from sympy.keras.nn import Softmax
from sympy.concrete.reduced import ReducedArgMax, ReducedSum
from sympy.tensor.tensor import TensorEqual


class SoftmaxClassifier(Module):

    def __init__(
            self,
            embed_size,
            units): 
        super().__init__()
        self.units = units
        self.embed_size = embed_size

        self.W = Symbol(real=True, shape=(embed_size, units))
        self.b = Symbol(real=True, shape=(self.units,))

    def forward(self, inputs):
        logits = Tanh(inputs @ self.W + self.b)
        log_softmax = Log(Softmax(logits))
        argmax = ReducedArgMax(log_softmax)
        return argmax, log_softmax

    @staticmethod
    def loss(y_true, y_pred):
        argmax, y_pred, *mask = y_pred
        mask = mask[0] if mask else None
        
        y_true = nn.functional.one_hot(y_true, y_pred.shape[-1])
        
        if mask is None:
            valid_positions = y_true.shape[1]
            loss = -ReducedSum(ReducedSum(y_true * y_pred)) / valid_positions
        else:
            valid_positions = ReducedSum(mask)
            loss = -ReducedSum(ReducedSum(y_true * y_pred) * mask) / valid_positions
            
        return loss
        
    @staticmethod
    def accuracy(y_true, y_pred):
        y_pred, embedding, *mask = y_pred
        mask = mask[0] if mask else None
                
        judge = TensorEqual(y_pred, y_true)
        if mask is not None: 
            judge |= ~mask
            
        return ReducedSum(judge)

