from ...Type import *
from ...Inductive import *
from ...Prelude import *
# from ...Prelude import Nat


class List(Inductive):

    def __new__(cls, *args):
        if not args:
            return cls.nil
        head, *tail = args
        α = cls.__annotations__['cons'][0]
        if not isinstance(head, α):
            head = α(head)
        return cls.cons(head, cls(*tail))

    α = Type
    # `[]` is the empty list.
    nil = Self
    # If `a : α` and `l : List α`, then `cons a l`, or `a :: l`, is the list whose first element is `a` and with `l` as the rest of the list.
    cons: (α, Self) = Self  # type: ignore

    def __str__(self):
        return '[%s]' % ", ".join(str(arg) for arg in self)
    
    def __len__(self):
        if self is self.nil:
            return 0
        head, tail = self.args
        return int(Nat.succ(len(tail)))
    
    def __getitem__(self, key):
        if not self:
            raise IndexError
        head, tail = self.args
        if key == 0:
            return head
        return tail[key - 1]
    
    def __iter__(self):
        while self is not self.nil:
            head, self = self.args
            yield head

    # in Python, __bool__ will be defined automatically if __len__ is defined
    # here, __bool__ is defined to facilitate the use of `not` operator
    def __bool__(self):
        return self is not self.nil
