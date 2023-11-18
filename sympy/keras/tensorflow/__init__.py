from tensorflow.python.ops import control_flow_ops, tensor_array_ops
import tensorflow as tf
import os

from sympy.keras.utility import availableGPU

def initialize():
    os.environ["CUDA_DEVICE_ORDER"] = "PCI_BUS_ID"
    
    CUDA_VISIBLE_DEVICES = os.environ.get('CUDA_VISIBLE_DEVICES')
    if CUDA_VISIBLE_DEVICES == '-1':
        print('use cpu memory')
    else:
        print('use gpu device')
        os.environ["CUDA_VISIBLE_DEVICES"] = str(availableGPU())
        gpus = tf.config.list_physical_devices('GPU')
        if gpus:
            try:
                # Currently, memory growth needs to be the same across GPUs
                for gpu in gpus:
                    tf.config.experimental.set_memory_growth(gpu, True)
                logical_gpus = tf.config.experimental.list_logical_devices('GPU')
                print(len(gpus), "Physical GPUs,", len(logical_gpus), "Logical GPUs")
            except RuntimeError as e:
                # Memory growth must be set before GPUs have been initialized
                print(e)

# perform y = func(x)
def while_loop(size, func, *args, **kwargs):

    def transform(x, stack=True, transpose=True):
        if stack:
            x = x.stack()

        if transpose:
            shape = [*range(len(x.shape))]
            shape[0], shape[1] = shape[1], shape[0]
            return tf.transpose(x, shape)
        else:
            return x

    def make_tuple(x):
        if isinstance(x, (tuple, list)):
            return x
        return (x,)

    if 'reverse' in kwargs and kwargs['reverse']:
        if 'start' in kwargs:
            start = kwargs['start']
        else:
            start = -1
        stop = start - size
        _, *args = control_flow_ops.while_loop(lambda i, *_: i > stop ,
                                               lambda i, *args:(i - 1, *make_tuple(func(i, *args))),
                                               loop_vars=(start, *args))
    else:
        if 'start' in kwargs:
            start = kwargs['start']
        else:
            start = 0
        stop = start + size

        _, *args = control_flow_ops.while_loop(lambda i, *_: i < stop,
                                               lambda i, *args:(i + 1, *make_tuple(func(i, *args))),
                                               loop_vars=(start, *args))
    transpose = 'transpose' in kwargs and kwargs['transpose']
    stack = 'stack' not in kwargs or kwargs['stack']

    args = [transform(arg, stack, transpose) if isinstance(arg, tensor_array_ops.TensorArray) else arg for arg in args]
    return args[0] if len(args) == 1 else args

