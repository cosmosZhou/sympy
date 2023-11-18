import numpy as np
import torch

def iostream(self, g, prefix='', mode='r'):
    name = self._get_name()
    if prefix:
        name = f"{prefix}/{name}"
    
    for weight_name, symbolic_weight in self._parameters.items():
        if symbolic_weight is None:
            continue
        
        if mode == 'r':
            weight = np.asarray(g[weight_name])
            tensor_shape = tuple(symbolic_weight.shape)
            if tensor_shape != weight.shape:
                print(name + '.' + weight_name if name else weight_name, ': reshape from %s to %s' % (weight.shape, tensor_shape))
                [*w] = weight.reshape((-1,))
                from functools import reduce
                sizeWanted = reduce(lambda a, b : a * b, tensor_shape)
                x = w * (sizeWanted // len(w)) + w[:sizeWanted % len(w)]
                weight = np.array(x).reshape(tensor_shape)
                    
            weight = torch.from_numpy(weight)
            if symbolic_weight.is_cuda:
                weight = weight.cuda()
            symbolic_weight[:] = weight
            
        elif mode == 'w':
            weight = symbolic_weight.detach().cpu().numpy()
            param_dset = g.create_dataset(weight_name, weight.shape, dtype=weight.dtype)
            if weight.shape:
                param_dset[:] = weight
            else:
                param_dset[()] = weight
        
    for module_name, module in self._modules.items():
        if [*module.parameters()]:
            iostream(module, g[module_name] if mode == 'r' else g.create_group(module_name), prefix=name, mode=mode)
    

