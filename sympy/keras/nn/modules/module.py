from _collections import OrderedDict
from typing import Optional
from sympy.core.symbol import Symbol
import re
import functools

class Module:
    
    def __init__(self):
        self._weights = OrderedDict()
        self._modules = OrderedDict()
        self._output_name = self._get_name()
        self.substitution = {}
        # self._hook_for_profile()

    def _assumption_clear_cache(self, cacheType, x):
        for sym in self.substitution:
            sym._assumption_clear_cache(cacheType, x)

    def make_substitutions(self):
        for sym, definition in self.substitution.items():
            assert 'definition' not in sym._assumptions
            sym._assumptions['definition'] = definition
        
        for module in self._modules.values():
            module.make_substitutions()            
    
    def load_weights(self, h5):
        state_dict = {}
        import numpy as np
        for name, weight in self._weights.items():
            try:
                state_dict[weight] = np.array(h5[name])
            except KeyError:
                print(weight, "is not initialized properly")
                state_dict[weight] = np.random.rand(*weight.shape)
                
        for name, module in self._modules.items():
            state_dict |= module.load_weights(h5[name])
            
        return state_dict
    
    def _hook_for_profile(self):
        def profile_hook_forward(func):

            @functools.wraps(func)
            def wrapper(self, *args, **kwargs):
                y = func(self, *args, **kwargs)
                if isinstance(y, tuple):
                    if len(y) == 2:
                        y, mask = y
                        if not isinstance(y, Symbol):
                            y = Symbol("Y_" + self._output_name, substitution=y, dtype=y.dtype, shape=y.shape)
                        return y, mask
                    assert False
                else:
                    if not isinstance(y, Symbol):
                        y = Symbol("Y_" + self._output_name, substitution=y, dtype=y.dtype, shape=y.shape)
                    return y

            return wrapper

        if hasattr(self.__class__, 'forward'):
            hooked = getattr(self.__class__.forward, "hooked", None)
            if not hooked:
                self.__class__.forward = profile_hook_forward(self.__class__.forward)
                self.__class__.forward.hooked = True


    @staticmethod
    def _addindent(s_, numSpaces):
        s = s_.split('\n')
        # don't do anything for single-line stuff
        if len(s) == 1:
            return s_
        first = s.pop(0)
        s = [(numSpaces * ' ') + line for line in s]
        s = '\n'.join(s)
        s = first + '\n' + s
        return s
        
    def extra_repr(self) -> str:
        r"""Set the extra representation of the module

        To print customized extra information, you should re-implement
        this method in your own modules. Both single-line and multi-line
        strings are acceptable.
        """
        return ''
        
    def append_weight_prefix(self, prefix):
        '''
        prefix is the classname of self's parent
        '''
        
        if not prefix:
            return
        
        for name, symbol in self._weights.items():
            m = re.fullmatch(r'((?:\w|\\_)+?)((?:_\w+)+)', symbol.name)
            assert m, symbol.name
            name, prefixes = m.groups()
            symbol.name = f"{name}_{prefix}{prefixes}"
            
        for name, module in self._modules.items():
            module.append_weight_prefix(prefix)
            
    def append_module_prefix(self, prefix):
        '''
        prefix is the classname of self's parent
        '''
        
        if prefix:
            if not self._output_name.startswith(prefix):
                self._output_name = f"{prefix}_{self._output_name}"
        
            for _, module in self._modules.items():
                module.append_module_prefix(prefix)
            
    def __repr__(self):
        # We treat the extra repr like the sub-module, one item per line
        extra_lines = []
        extra_repr = self.extra_repr()
        # empty string will be split into list ['']
        if extra_repr:
            extra_lines = extra_repr.split('\n')
        child_lines = []
        for key, module in self._modules.items():
            mod_str = repr(module)
            mod_str = self._addindent(mod_str, 2)
            child_lines.append('(' + key + '): ' + mod_str)
        lines = extra_lines + child_lines

        main_str = self._get_name() + '('
        if lines:
            # simple one-liner info, which most builtin Modules will use
            if len(extra_lines) == 1 and not child_lines:
                main_str += extra_lines[0]
            else:
                main_str += '\n  ' + '\n  '.join(lines) + '\n'

        main_str += ')'
        return main_str

    def __dir__(self):
        module_attrs = dir(self.__class__)
        attrs = list(self.__dict__.keys())
        weights = list(self._weights.keys())
        modules = list(self._modules.keys())

        keys = module_attrs + attrs + weights + modules

        # Eliminate attrs that are not legal Python variable names
        keys = [key for key in keys if not key[0].isdigit()]

        return sorted(keys)
        
    def _weight_prefix(self):
        return self._get_name()
    
    def _get_name(self):
        return self.__class__.__name__
        
    def __call__(self, *args, **kwargs):
        y = self.forward(*args, **kwargs)
        if isinstance(y, (tuple, list)):
            outputs = [*y]
            for i, y in enumerate(y):
                if isinstance(y, (tuple, list)):
                    for j, y in enumerate(y):
                        if y is not None and not isinstance(y, Symbol):
                            sym = Symbol(f"Y_{i}_{j}_" + self._output_name, shape=y.shape, **y.dtype.dict)
                            outputs[i] = sym
                            assert sym not in self.substitution
                            self.substitution[sym] = y
                else:
                    if y is not None and not isinstance(y, Symbol):
                        sym = Symbol(f"Y_{i}_" + self._output_name, shape=y.shape, **y.dtype.dict)
                        outputs[i] = sym
                        assert sym not in self.substitution
                        self.substitution[sym] = y

            return outputs
                
        if not isinstance(y, Symbol):
            sym = Symbol("Y_" + self._output_name, shape=y.shape, **y.dtype.dict)
            assert sym not in self.substitution
            self.substitution[sym] = y
            return sym
            
        return y
    
    def __getattr__(self, name: str):
        if '_weights' in self.__dict__:
            _weights = self.__dict__['_weights']
            if name in _weights:
                return _weights[name]

        if '_modules' in self.__dict__:
            modules = self.__dict__['_modules']
            if name in modules:
                return modules[name]
            
        raise AttributeError("'{}' object has no attribute '{}'".format(
            type(self).__name__, name))
    
    def __setattr__(self, name: str, value) -> None:
        def remove_from(*dicts_or_sets):
            for d in dicts_or_sets:
                if name in d:
                    if isinstance(d, dict):
                        del d[name]
                    else:
                        d.discard(name)

        params = self.__dict__.get('_weights')
        if isinstance(value, Symbol):
            if params is None:
                raise AttributeError(
                    "cannot assign weights before Module.__init__() call")
            remove_from(self.__dict__, self._modules)
            self.register_weight(name, value)
        elif params is not None and name in params:
            if value is not None:
                raise TypeError("cannot assign '{}' as weight '{}' "
                                "(torch.nn.Parameter or None expected)"
                                .format(torch.typename(value), name))
            self.register_weight(name, value)
        else:
            modules = self.__dict__.get('_modules')
            if isinstance(value, Module):
                if modules is None:
                    raise AttributeError(
                        "cannot assign module before Module.__init__() call")
                remove_from(self.__dict__, self._weights)
                modules[name] = value
                value.append_weight_prefix(self._weight_prefix())
                value.append_module_prefix(name)
            elif modules is not None and name in modules:
                if value is not None:
                    raise TypeError("cannot assign '{}' as child module '{}' "
                                    "(torch.nn.Module or None expected)"
                                    .format(torch.typename(value), name))
                modules[name] = value
            else:
                object.__setattr__(self, name, value)    
        
    def register_weight(self, name: str, param: Optional[Symbol]) -> None:
        r"""Adds a weight to the module.

        The weight can be accessed as an attribute using given name.

        Args:
            name (string): name of the weight. The weight can be accessed
                from this module using the given name
            param (Parameter): weight to be added to the module.
        """
        if '_weights' not in self.__dict__:
            raise AttributeError(
                "cannot assign weight before Module.__init__() call")

        elif not isinstance(name, str):
            raise TypeError("weight name should be a string. "
                            "Got {}".format(torch.typename(name)))
        elif '.' in name:
            raise KeyError("weight name can't contain \".\"")
        elif name == '':
            raise KeyError("weight name can't be empty string \"\"")
        elif hasattr(self, name) and name not in self._weights:
            raise KeyError("attribute '{}' already exists".format(name))

        if param is None:
            self._weights[name] = None
        elif not isinstance(param, Symbol):
            raise TypeError("cannot assign '{}' object to weight '{}' "
                            "(torch.nn.Parameter or None required)"
                            .format(torch.typename(param), name))
        else:
            attr = name
            if '_' in name:
                name = name.replace('_', f'\_')
                
            param.name = name + '_' + self._get_name()
            self._weights[attr] = param
    
    def add_module(self, name: str, module: Optional['Module']) -> None:
        self._modules[name] = module
        module.append_weight_prefix(name)
        module.append_module_prefix(name)
    
    def get_submodule(self, target: str) -> "Module":
        """
        Returns the submodule given by ``target`` if it exists,
        otherwise throws an error.

        For example, let's say you have an ``nn.Module`` ``A`` that
        looks like this:

        .. code-block::text

            A(
                (net_b): Module(
                    (net_c): Module(
                        (conv): Conv2d(16, 33, kernel_size=(3, 3), stride=(2, 2))
                    )
                    (linear): Linear(in_features=100, out_features=200, bias=True)
                )
            )

        (The diagram shows an ``nn.Module`` ``A``. ``A`` has a nested
        submodule ``net_b``, which itself has two submodules ``net_c``
        and ``linear``. ``net_c`` then has a submodule ``conv``.)

        To check whether or not we have the ``linear`` submodule, we
        would call ``get_submodule("net_b.linear")``. To check whether
        we have the ``conv`` submodule, we would call
        ``get_submodule("net_b.net_c.conv")``.

        The runtime of ``get_submodule`` is bounded by the degree
        of module nesting in ``target``. A query against
        ``named_modules`` achieves the same result, but it is O(N) in
        the number of transitive modules. So, for a simple check to see
        if some submodule exists, ``get_submodule`` should always be
        used.

        Args:
            target: The fully-qualified string name of the submodule
                to look for. (See above example for how to specify a
                fully-qualified string.)

        Returns:
            torch.nn.Module: The submodule referenced by ``target``

        Raises:
            AttributeError: If the target string references an invalid
                path or resolves to something that is not an
                ``nn.Module``
        """
        if target == "":
            return self

        atoms: List[str] = target.split(".")
        mod: torch.nn.Module = self

        for item in atoms:

            if not hasattr(mod, item):
                raise AttributeError(mod._get_name() + " has no "
                                     "attribute `" + item + "`")

            mod = getattr(mod, item)

            if not isinstance(mod, torch.nn.Module):
                raise AttributeError("`" + item + "` is not "
                                     "an nn.Module")

        return mod

    def get_weight(self, target: str) -> "Parameter":
        """
        Returns the weight given by ``target`` if it exists,
        otherwise throws an error.

        See the docstring for ``get_submodule`` for a more detailed
        explanation of this method's functionality as well as how to
        correctly specify ``target``.

        Args:
            target: The fully-qualified string name of the Parameter
                to look for. (See ``get_submodule`` for how to specify a
                fully-qualified string.)

        Returns:
            torch.nn.Parameter: The Parameter referenced by ``target``

        Raises:
            AttributeError: If the target string references an invalid
                path or resolves to something that is not an
                ``nn.Parameter``
        """
        module_path, _, param_name = target.rpartition(".")

        mod = self.get_submodule(module_path)

        if not hasattr(mod, param_name):
            raise AttributeError(mod._get_name() + " has no attribute `"
                                 + param_name + "`")

        param: torch.nn.Parameter = getattr(mod, param_name)

        if not isinstance(param, torch.nn.Parameter):
            raise AttributeError("`" + param_name + "` is not an "
                                 "nn.Parameter")

        return param

