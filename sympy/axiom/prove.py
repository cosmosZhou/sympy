import os
import re
from sympy import axiom  # @UnusedImport


from sympy import utility
import traceback
from sympy.utilities.misc import Text

count = 0


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

                __init__ = '/'.join(path[:index - 1]) + '/' + package.replace('.', '/') + '/__init__.py'
                print('editing', __init__)

                Text(__init__).append('from . import %s' % module)
                return

            try:
                global count
                count += 1

                if not package.prove():
                    print(package, 'is not yet proven')

            except Exception as e:
                print(package)
                traceback.print_exc()

        elif os.path.isdir(path):
            readFolder(path, sufix)


if __name__ == '__main__':
    utility.batch_proving = True
    rootdir = os.path.dirname(__file__)
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)
        arr = []

        if os.path.isdir(path):
            arr = readFolder(path)

    print('in all %d axioms' % count)
