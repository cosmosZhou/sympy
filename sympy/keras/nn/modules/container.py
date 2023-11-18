from .module import Module
from typing import Iterable, Optional, Iterator
from _collections import OrderedDict
        
class ModuleList(Module):
    r"""Holds submodules in a list.

    :class:`~torch.nn.ModuleList` can be indexed like a regular Python list, but
    modules it contains are properly registered, and will be visible by all
    :class:`~torch.nn.Module` methods.

    Args:
        modules (iterable, optional): an iterable of modules to add

    Example::

        class MyModule(nn.Module):
            def __init__(self):
                super(MyModule, self).__init__()
                self.linears = nn.ModuleList([nn.Linear(10, 10) for i in range(10)])

            def forward(self, x):
                # ModuleList can act as an iterable, or be indexed using ints
                for i, l in enumerate(self.linears):
                    x = self.linears[i // 2](x) + l(x)
                return x
    """

    def __init__(self, modules: Optional[Iterable[Module]] = None) -> None:
        super(ModuleList, self).__init__()
        if modules is not None:
            self += modules

    def _get_abs_string_index(self, idx):
        """Get the absolute index for the list of modules"""
        idx = operator.index(idx)
        if not (-len(self) <= idx < len(self)):
            raise IndexError('index {} is out of range'.format(idx))
        if idx < 0:
            idx += len(self)
        return str(idx)

    def __getitem__(self, idx: int) -> Module:
        if isinstance(idx, slice):
            return self.__class__(list(self._modules.values())[idx])
        else:
            return self._modules[self._get_abs_string_index(idx)]

    def __setitem__(self, idx: int, module: Module) -> None:
        idx = self._get_abs_string_index(idx)
        return setattr(self, str(idx), module)

    def __delitem__(self, idx) -> None:
        if isinstance(idx, slice):
            for k in range(len(self._modules))[idx]:
                delattr(self, str(k))
        else:
            delattr(self, self._get_abs_string_index(idx))
        # To preserve numbering, self._modules is being reconstructed with modules after deletion
        str_indices = [str(i) for i in range(len(self._modules))]
        self._modules = OrderedDict(list(zip(str_indices, self._modules.values())))

    def __len__(self) -> int:
        return len(self._modules)

    def __iter__(self) -> Iterator[Module]:
        return iter(self._modules.values())

    def __iadd__(self, modules: Iterable[Module]) -> 'ModuleList':
        return self.extend(modules)

    def __dir__(self):
        keys = super(ModuleList, self).__dir__()
        keys = [key for key in keys if not key.isdigit()]
        return keys

    def insert(self, index: int, module: Module) -> None:
        r"""Insert a given module before a given index in the list.

        Args:
            index (int): index to insert.
            module (nn.Module): module to insert
        """
        for i in range(len(self._modules), index, -1):
            self._modules[str(i)] = self._modules[str(i - 1)]
        self._modules[str(index)] = module

    def append(self, module: Module) -> 'ModuleList':
        r"""Appends a given module to the end of the list.

        Args:
            module (nn.Module): module to append
        """
        self.add_module(str(len(self)), module)
        return self

    def extend(self, modules: Iterable[Module]) -> 'ModuleList':
        r"""Appends modules from a Python iterable to the end of the list.

        Args:
            modules (iterable): iterable of modules to append
        """
        offset = len(self)
        for i, module in enumerate(modules):
            self.add_module(str(offset + i), module)
        return self

    # remove forward alltogether to fallback on Module's _forward_unimplemented
        
