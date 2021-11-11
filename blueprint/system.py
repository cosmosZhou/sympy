from flask.blueprints import Blueprint
from util import std
from flask.globals import request

system = Blueprint('system', __name__, static_folder='../static')


@system.route('/favicon.ico')
def favicon():
    return system.send_static_file('favicon.ico')

# @system.route('/kill', methods=['POST', 'GET'])
# def kill():
#     import os
#     pid = os.getpid()
#     if std.is_Linux():
#         os.system(f"kill -9 {pid}")
#     else:
#         os.system(f"taskkill /F /pid {pid}")
#     return ""


@system.route('/kill', methods=['GET'])
def kill():
    import signal
    import os
    os.kill(os.getpid(), signal.SIGILL)
    return std.json_encode({'text': 'kill myself'})

    
@system.route('/eval', methods=['POST', 'GET'])
def evaluate():
#     decode = request.args.get('decode')
#     if decode is None:
#         decode = request.form.get('decode')

    python = request.args.get('python')
    if python is None:
        python = request.form.get('python')

    text = request.args.get('text')
    if text is None:
        text = request.form.get('text')

#     print('python code:')
#     print(python)

    result = eval(python)
    
#     print('result =', result)
    if text is None: 
        return std.json_encode(result)
    return result


@system.route('/system/user')
def system_user():
    from util.utility import user
    return user
