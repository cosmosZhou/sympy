import re
from util import MySQL

keywords = ['False', 'None', 'True', 
            'and', 'as', 'assert', 
            'break', 
            'case', 'class', 'continue', 
            'def', 'del', 
            'elif', 'else', 'except', 
            'finally', 'for', 
            'if', 'import', 'in', 'isinstance', 
            'or', 
            'raise', 'return', 
            'self', 'super', 
            'try', 
            'while', 'with', 
            'yield']

sections = ['algebra', 'calculus', 'discrete', 'geometry', 'keras', 'sets', 'stats']

# from sympy import *
import sympy
if __name__ == '__main__':
    vocab = keywords + sections    
    
    for key, value in sympy.__dict__.items():
        if re.match('^[A-Za-z]', key):
            vocab.append(key)        

#     print(vocab)
    
    data = []
    
    print('max len = ', max(len(v) for v in vocab))
    for word in vocab:
        length = len(word)
        for i in range(1, length - 1):
            data.append((word[:i], word, 1))
    
    for key, value, *_ in data:
        print(key, '=>', value)
        
    print(len(data))
    
    sql = '''\
CREATE TABLE `tbl_hint_py` (
  `prefix` varchar(36) NOT NULL,
  `phrase` varchar(36) NOT NULL,
  `usage` int(11) DEFAULT '1',
  PRIMARY KEY (`prefix`,`phrase`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci 
PARTITION BY KEY ()
PARTITIONS 8    
    '''
    try:
        MySQL.instance.execute(sql)
    except Exception as e:
        print(e)
    
    MySQL.instance.load_data('tbl_hint_py', data)
