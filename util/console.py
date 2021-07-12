from wsgiref import simple_server
from util import *    
import regex as re
from flask import Flask, render_template, jsonify
import os
 
app = Flask(__name__)

 
@app.route('/')
def hello_world():
    return "<h1 style='color:red' algin='center'>Hello World!<h1>"


@app.route('/main/')
def westos():
    # 如何在flask程序中返回一个html页面；flask默认查找页面内容的位置为templates目录；
    return render_template('main.html')

 
tasks = [
    {
        'id': 1,
        'title': u'Buy groceries',
        'description': u'Milk, Cheese, Pizza, Fruit, Tylenol',
        'done': False
    },
    {
        'id': 2,
        'title': u'Learn Python',
        'description': u'Need to find a good Python tutorial on the web',
        'done': False
    }]

 
@app.route('/restful/getTask', methods=['GET'])
def get_tasks():
    return jsonify({'tasks':tasks})


@app.route('/kill', methods=['GET'])
def kill():
    import signal
    os.kill(os.getpid(), signal.SIGILL)
    return jsonify({'text': 'kill myself'})


from flask import request

__locals__ = {}


@app.route('/eval', methods=['POST', 'GET'])
def evaluate():
    
    python = request.args.get('py')
    if python is None:
        python = request.form.get('py')

    text = request.args.get('text')
    if text is None:
        text = request.form.get('text')

    callback = request.args.get('callback')
    if callback is None:
        callback = request.form.get('callback')

    try:
        result = eval(python, globals(), __locals__)
    except SyntaxError: 
        m = re.match('(\w+) *=(.+)', python)
        assert m
        var = m[1]
        exec(python, globals(), __locals__)
        # globals[var] = eval(var)        
        return f"{callback}({{'latex': ''}})"
    except NameError as e:
        print(e)
        e = str(e)
        e = e.replace("'", "\\'")
        return f"{callback}({{'latex': 'NameError: {e}'}})"
    except Exception as e:
        print(e)
        e = str(e)
        e = e.replace("'", "\\'")
        return f"{callback}({{'latex': '{e}'}})"
    
#     print('result =', result)
    if text is None:
        from util.std import json_encode        
        return json_encode(latex)

    print(callback)
    if isinstance(result, Basic):
        latex = r'$$%s$$' % result.latex.replace('\\', '\\\\').replace("'", "\\'")        
    else:
        latex = str(result)
        
    if callback is None:
        return latex
    return f"{callback}({{'latex': '{latex}'}})"


@app.route('/restful/postTask', methods=['POST'])
def post_tasks():
    return jsonify({'tasks':tasks})


def run(port):
    httpd = simple_server.make_server('0.0.0.0', port, app)
    httpd.serve_forever()

        
if __name__ == '__main__':
    run(5000)
