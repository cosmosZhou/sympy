import requests
import json
from util import MySQL


def compare():
    local_dic = {axiom : timestamp for axiom, timestamp in json.loads(s.get("http://localhost/sympy/php/request/timestamp.php").text)}
    remote_dic = {axiom : timestamp for axiom, timestamp in json.loads(s.get("https://www.axiom.top/sympy/php/request/timestamp.php").text)}
    for key in local_dic.keys() & remote_dic.keys():
        assert local_dic[key] == remote_dic[key]
    return True
    
if __name__ == '__main__':
    s = requests.session()
    result = s.get("https://www.axiom.top/sympy/php/request/timestamp.php")
    seq_param = json.loads(result.text)
    
    seq_param = [(timestamp, axiom) for axiom, timestamp in seq_param]
    
    MySQL.instance.executemany(f'update tbl_axiom_py set timestamp = %s where axiom = %s and user = "{MySQL.user}"', seq_param)
    
    assert compare()
# exec(open('./util/function.py').read())