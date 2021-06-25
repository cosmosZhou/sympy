import json

def json_encode(data, utf8=False): 
    s = json.dumps(data, ensure_ascii=False)
    if utf8:
        s = s.encode(encoding='utf-8')
    return s 


