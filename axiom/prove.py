import os
import re
import axiom  # @UnusedImport
from sympy import utility
import traceback
from sympy.utilities.misc import Text

count = 0

unproven = []

erroneous = []


def readFolder(rootdir, sufix='.py'):
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)

        if path.endswith(sufix):
            name = name[:-len(sufix)]
            if name == '__init__':
                continue

            print('testing ', path)
            path = re.compile(r'[\\/]+').split(path[:-len(sufix)])
#             print(path)
            index = path.index('axiom')

            package = '.'.join(path[index:])
            try:
                package = eval(package)
            except AttributeError as e:
                print(e)
                s = str(e)

                m = re.compile("module '([\w\.]+)' has no attribute '(\w+)'").fullmatch(s)
                assert m
                package, module = m.groups()

                __init__ = '/'.join(path[:index]) + '/' + package.replace('.', '/') + '/__init__.py'
                print('editing', __init__)

                Text(__init__).append('from . import %s' % module)
                return

            global count
            count += 1

            ret = package.prove(package.__file__)
            if ret is False:
                unproven.append(package)
            elif ret is None:
                erroneous.append(package)

        elif os.path.isdir(path):
            readFolder(path, sufix)


if __name__ == '__main__':
    rootdir = os.path.dirname(__file__)
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)
        arr = []

        if os.path.isdir(path):
            arr = readFolder(path)

    print('in all %d axioms' % count)

    if unproven:
        print('unproven axioms')
        for p in unproven:
            print(p)

    if erroneous:
        print('erroneous axioms')
        for p in erroneous:
            print(p)
