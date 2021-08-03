import json
import os

def json_encode(data, utf8=False): 
    s = json.dumps(data, ensure_ascii=False)
    if utf8:
        s = s.encode(encoding='utf-8')
    return s 


def eol_convert(fileName):
    with open(fileName, "rb") as f:
        data = bytearray(os.path.getsize(fileName))
        f.readinto(data)
        # print(data)
        data = data.replace(b"\r\n", b"\n")

    with open(fileName, "wb") as f:
        # print(data)
        f.write(data)    

