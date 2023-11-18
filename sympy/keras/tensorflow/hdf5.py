import numpy as np, regex as re

from tensorflow.python.ops import variables
from keras.engine.sequential import Sequential

def iostream(self, g, prefix='', mode='r', name=None):
    if name is None:
        name = self.name

    if prefix:
        name = f"{prefix}/{name}"
    
    for symbolic_weight in self._flatten(recursive=False, predicate=lambda obj : isinstance(obj, variables.Variable), expand_composites=True):
        assert re.search(":0$", symbolic_weight.name)
        if symbolic_weight.name.startswith(name):
            weight_name = re.search(f"{name}/(.+):0$", symbolic_weight.name)[1]
        else:
            print(f"{symbolic_weight.name} should startswith: \n{name}")
            
            symbolic_tokens = symbolic_weight.name[:-2].split('/')
            tokens = name.split('/')
            
            sufix = []
            i = len(symbolic_tokens) - 1
            j = len(tokens) - 1
            while True:
                if symbolic_tokens[i] != tokens[j]:
                    sufix.append(symbolic_tokens[i])
                else:
                    break
                i -= 1
                
            sufix.reverse()
            weight_name = '/'.join(sufix)
        
        if mode == 'r':
            weight = np.asarray(g[weight_name])
            tensor_shape = tuple(symbolic_weight.shape)
            if tensor_shape != weight.shape:
                print(name + '.' + weight_name if name else weight_name, ': reshape from %s to %s' % (weight.shape, tensor_shape))
                if len(weight.shape) > len(tensor_shape):
                    weight = weight[[0] * (len(weight.shape) - len(tensor_shape))]
                elif len(weight.shape) < len(tensor_shape):
                    for _ in range(len(tensor_shape) - len(weight.shape)):
                        weight = np.expand_dims(weight, axis=0)
                    
                for i, (w_shape, t_shape) in enumerate(zip(weight.shape, tensor_shape)):
                    if w_shape > t_shape:
                        weight = weight[(slice(None),) * i + (slice(None, t_shape),)]
                    elif w_shape < t_shape:
                        quo = t_shape // w_shape
                        rem = t_shape % w_shape
                        weight = np.tile(weight, [1] * i + [quo] + [1] * (len(weight.shape) - 1 - i))
                        if rem:
                            weight = np.concatenate([weight, weight[(slice(None),) * i + (slice(None, rem),)]], axis=i)
                    
            symbolic_weight.assign(weight)
            
        elif mode == 'w':
            weight = symbolic_weight.numpy()
            param_dset = g.create_dataset(weight_name, weight.shape, dtype=weight.dtype)
            if weight.shape:
                param_dset[:] = weight
            else:
                param_dset[()] = weight
    
    if isinstance(self, Sequential):
        for i, module in enumerate(self.layers):
            if module.variables:
                modele_name = str(i)
                iostream(module, g[modele_name] if mode == 'r' else g.create_group(modele_name), prefix=name, mode=mode, name=modele_name)
            
    else:
        for module in self._flatten_modules(recursive=False, include_self=False):
            if module.variables:
                if mode == 'r':
                    try:
                        iostream(module, g[module.name], prefix=name, mode=mode)
                    except KeyError as e: 
                        print(e)
                else:
                    iostream(module, g.create_group(module.name), prefix=name, mode=mode)
    

