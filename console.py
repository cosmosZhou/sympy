from wsgiref import simple_server
from flask import Flask, render_template, jsonify

from util import * 
from axiom import *
from util import MySQL    
import regex as re
import os, json
 
app = Flask(__name__)


@app.route('/')
def hello_world():
    return "<h1 style='color:red' algin='center'>Hello World!<h1>"


@app.route('/main/')
def westos():
    return render_template('main.html')
 
 
@app.route('/<symbol>')
def console(symbol):
    
    statements = []
    for script, latex in MySQL.instance.select(f"select script, latex from tbl_console_py where symbol = '{symbol}'"):
        latex = latex.strip()
        latex = json.loads(latex)
        
        script = json.loads(script)

        for i in range(len(latex)):
            statements.append(dict(script=script[i], latex=latex[i]))
        script = '\n'.join(script)
    
    statements.append(dict(script='', latex=''))
    
    return render_template('console.html', symbol=symbol, statements=statements, script=script)

 
@app.route('/kill', methods=['GET'])
def kill():
    import signal
    os.kill(os.getpid(), signal.SIGILL)
    return jsonify({'text': 'kill myself'})


from flask import request

__globals__ = globals()

    
def local_eval(python, __globals__): 
    try:
        result = eval(python, __globals__)
    except SyntaxError: 
        try:
            exec(python, __globals__)
        except Exception as e:
            return str(e)
    
        return ''

    except Exception as e:
        try:
            print(e)
            e = str(e)
            return e
        except:
            return str(type(e))        
    
    try:
        if isinstance(result, type) or not hasattr(result, "is_Basic"):
            latex = str(result)
        else:
            latex = r'\[%s\]' % result.latex
    except Exception as e:
        print(e)
        latex = f"{type(e).__name__}: {e}"
        
    return latex

        
@app.route('/eval', methods=['POST', 'GET'])
def evaluate():
    python = request.json.get('py')

    if request.json.get('multiple'):
        python = python.splitlines()
        latex = [local_eval(line, __globals__) for line in python]
        
        return utility.json_encode(latex)

    else:
        try:
            result = eval(python, __globals__)
        except SyntaxError:
            exec(python, __globals__)
            return ''
        except Exception as e:
            typname = type(e).__name__
            print(type(e), e)
            msg = str(e)
                    
            return f'{typname}: {msg}'
    
    if isinstance(result, type) or not hasattr(result, "is_Basic"):
        latex = str(result)
    else:
        latex = r'\[%s\]' % result.latex        
    return latex    

def extract_latex(symbol):
    symbol = globals()[symbol]
    
    doc = symbol.__doc__
    if doc is None:
        return None
    
    lines = []
    for line in doc.splitlines():
        m = re.match("^ *>>> *(.+)", line)
        if m:
            line = m[1]
            if re.match("^from +\S+ +import +.+", line):
                continue
            lines.append(line)
            continue
        m = re.match("^ *\.\.\. *(.+)", line)
        if m:
            if not lines:
                continue
                
            line = lines[-1]
            line += '\n' + m[1]
            lines[-1] = line
            
    return lines

    
@app.route('/hint', methods=['POST', 'GET'])
def hint():
    
    symbol = request.args.get('symbol')
    if symbol is None:
        symbol = request.form.get('symbol')

    return utility.json_encode(extract_latex(symbol))


@app.route('/restful/postTask', methods=['POST'])
def post_tasks():
    return jsonify({'tasks':tasks})


def run(port):
    httpd = simple_server.make_server('0.0.0.0', port, app)
    httpd.serve_forever()


if __name__ == '__main__':
    run(5000)
