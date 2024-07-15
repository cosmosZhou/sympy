import os, importlib
from colorama import Fore, Style


def find_test_files(directory):
    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.endswith("test.py"):
                yield os.path.join(root, file)

root = os.path.dirname(__file__) + '/Init/'
for file in find_test_files(root):
    try:
        module = importlib.import_module(
            'Init.' + file[len(root):-3].replace(os.path.sep, '.'),
            package='lean'
        )
        print(f"finish with: {Fore.GREEN}{module}{Style.RESET_ALL}")
    except Exception as e:
        print(e)
        print(f"error with: {Fore.RED}{file}{Style.RESET_ALL}")
        import traceback
        traceback.print_exc()
    
