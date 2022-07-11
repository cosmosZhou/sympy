from util import *


@apply
def apply(self):
    args = self.of(Add)
    common_terms = None
    for arg in args:
        if arg.is_Mul:
            if common_terms is None:
                common_terms = {*arg.args}
            else:
                common_terms &= {*arg.args}
        else:
            if common_terms is None:
                common_terms = {arg}
            else:
                common_terms &= {arg}
        if not common_terms:
            return

    factor = Mul(*common_terms)
    additives = []
    for arg in args:
        if arg.is_Mul:
            arg = Mul(*{*arg.args} - common_terms)
            additives.append(arg)
        else:
            assert arg == factor
            additives.append(1)

    return Equal(self, Add(*additives) * factor)


@prove
def prove(Eq):
    a, x, y = Symbol(complex=True)
    Eq << apply(a * x - a * y)

    Eq << Eq[0].this.rhs.expand()


if __name__ == '__main__':
    run()

from . import st
from . import together
# created on 2018-02-21
