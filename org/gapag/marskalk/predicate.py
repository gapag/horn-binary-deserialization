from dot_printer import *
class Predicate:
    field = None

    def __init__(self, field):
        self.field = field

    def dot_friendly_identifier(self, name):
        if isinstance(self, Pointer):
            v = str([self.field.getindex(), self.field.offset(),
                     self.field.landing()])
        else:
            v = str(self.field.getindex())
        return name + "_" + dot_friendly(v)+"_"

    def getindex(self):
        return self.field.getindex()


class Beg(Predicate):
    def __str__(self):
        return self.dot_friendly_identifier("beg")

    def __init__(self, field):
        Predicate.__init__(self, field)


class Len(Predicate):
    def __str__(self):
        return self.dot_friendly_identifier("len")

    def __init__(self, field):
        Predicate.__init__(self, field)


class Val(Predicate):
    def __str__(self):
        return self.dot_friendly_identifier("val")

    def __init__(self, field):
        Predicate.__init__(self, field)


class RepLen(Predicate):
    def __str__(self):
        return self.dot_friendly_identifier("repLen")

    def __init__(self, field):
        Predicate.__init__(self, field)


class Rep(Predicate):
    def __str__(self):
        return self.dot_friendly_identifier("rep")

    def __init__(self, field):
        Predicate.__init__(self, field)


class Pointer(Predicate):
    def __str__(self):
        return self.dot_friendly_identifier("ptr")

    def __init__(self, field):
        Predicate.__init__(self, field)