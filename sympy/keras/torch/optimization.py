import torch
from typing import Callable, Iterable, Tuple
from torch import nn
from torch.optim.lr_scheduler import LambdaLR
# from util.database import MySQL

class AdamW(torch.optim.Optimizer):
    """
    Implements Adam algorithm with weight decay fix as introduced in `Decoupled Weight Decay Regularization
    <https://arxiv.org/abs/1711.05101>`__.

    Parameters:
        params (:obj:`Iterable[nn.parameter.Parameter]`):
            Iterable of parameters to optimize or dictionaries defining parameter groups.
        lr (:obj:`float`, `optional`, defaults to 1e-3):
            The learning rate to use.
        betas (:obj:`Tuple[float,float]`, `optional`, defaults to (0.9, 0.999)):
            Adam's betas parameters (b1, b2).
        epsilon (:obj:`float`, `optional`, defaults to 1e-6):
            Adam's epsilon for numerical stability.
        weight_decay (:obj:`float`, `optional`, defaults to 0):
            Decoupled weight decay to apply.
    """

    def __init__(
        self,
        params: Iterable[nn.parameter.Parameter],
        lr: float = 2e-5,
        betas: Tuple[float, float] = (0.9, 0.999),
        epsilon: float = 1e-5,
        weight_decay: float = 0.01,
    ):
        if lr < 0.0:
            raise ValueError(f"Invalid learning rate: {lr} - should be >= 0.0")
        if not 0.0 <= betas[0] < 1.0:
            raise ValueError(f"Invalid beta parameter: {betas[0]} - should be in [0.0, 1.0[")
        if not 0.0 <= betas[1] < 1.0:
            raise ValueError(f"Invalid beta parameter: {betas[1]} - should be in [0.0, 1.0[")
        if not 0.0 <= epsilon:
            raise ValueError(f"Invalid epsilon value: {epsilon} - should be >= 0.0")
        defaults = dict(lr=lr, betas=betas, epsilon=epsilon, weight_decay=weight_decay)
        super().__init__(params, defaults)

    def parameters(self):
        for group in self.param_groups:
            for p in group["params"]:
                yield p
    
    @torch.no_grad()
    def step(self, closure: Callable = None):
        """
        Performs a single optimization step.

        Arguments:
            closure (:obj:`Callable`, `optional`): A closure that reevaluates the model and returns the loss.
        """
        loss = None
        if closure is not None:
            loss = closure()

        total_norm = torch.nn.utils.clip_grad_norm_(self.parameters(), 1)
        print("total_norm =", total_norm)
        if torch.isnan(total_norm):
            print("total_norm is nan, skipping...")
            return
        
        for group in self.param_groups:
            for p in group["params"]:
                if p.grad is None:
                    continue
                
                g = p.grad.data

                state = self.state[p]

                # State initialization
                if len(state) == 0:
                    state["step"] = 0
                    # Exponential moving average of gradient values
                    state["m_t"] = torch.zeros_like(p.data)
                    # Exponential moving average of squared gradient values
                    state["v_t"] = torch.zeros_like(p.data)

                m_t, v_t = state["m_t"], state["v_t"]
                
                beta_1, beta_2 = group["betas"]
                
                m_t = (beta_1 * m_t) + (1 - beta_1) * g
                v_t = (beta_2 * v_t) + (1 - beta_2) * g.square()
    
                update = m_t / (v_t.sqrt() + group["epsilon"])

                if len(p.shape) > 1:
                    update += group["weight_decay"] * p.data
                    
                p.data -= group["lr"] * update
                
                state["m_t"], state["v_t"] = m_t, v_t
                state["step"] += 1

        return loss


