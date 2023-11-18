
class Context:
    
    session = []
    
    def __init__(self, feeddict, **kwargs):
        backend, = kwargs
        setattr(self, backend, feeddict)
        
    def torch(self, sym):
        return self.torch.get(id(sym))
    
    def keras(self, sym):
        return self.keras.get(id(sym))
    
    def numpy(self, sym):
        return self.numpy.get(id(sym))
    
    def paddle(self, sym):
        return self.paddle.get(id(sym))
    
    def __enter__(self):
        Context.session.append(self)
        return self

    @classmethod
    def get(cls, sym, **kwargs):
        backend, = kwargs
        for context in reversed(cls.session):
            if (value := getattr(context, backend, sym)) is not None:
                return value
            
    def __exit__(self, *_):
        Context.session.pop()

    