class Field:
    index = []
    pass


class F(Field):
    length = 0

    def __init__(self, len):
        super(Field, self).__init__(self, )
        self.length = len


class V(Field):
    def __init__(self):
        pass


class R(Field):
    body = []

    def __init__(self, bo):
        self.body = bo


class P(Field):
    origin = []
    span = 0

    def __init__(self, o, s):
        self.origin = o
        self.span = s


def pattern(fields, ind = []) :
    for f in fields :
        if isinstance(f,R) :
            # continue below
            pattern(f.body, ind)
        