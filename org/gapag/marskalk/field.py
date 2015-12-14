class Field:
    index = []
    pass

    def getindex(self):
        return self.index


class F(Field):
    def __init__(self):
        pass


class V(Field):
    def __init__(self):
        pass


class R(Field):
    body = []

    def __init__(self, bo):
        self.body = bo

class End(Field):
    def __init__(self):
        pass

class P(Field):
    origin = F()
    land = F()
    span = 0

    def __init__(self, field,
                 s):
        # super(Field, self).__init__(self)
        self.origin = field
        self.span = s

    def offset(self):
        return self.origin.getindex()

    def landing(self):
        return self.land.getindex()


class PointerError(Exception):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return repr(self.value)


def check_pending_pointers(pending_pointers, scopes):
    filtered = []
    for f in pending_pointers:
        if f.offset():
            complete_pointer(f, scopes)
        else:
            filtered.append(f)
    return filtered


def complete_pointer(f, scopes):
    if len(f.offset()) <= len(f.index):  # if we're on the same scope
        f.land = scopes[len(f.offset())][f.offset()[
                                             -1] + f.span ]  # look at an upper scope and compute the value of the landing pad 
    else:  # Pointing to a field that is more nested
        raise PointerError('Pointing to a more nested field')


class LayoutError(Exception):
    pass


def pattern(fields, ind=[], scopes={}, pending_pointers=[]):  # linearized=[]
    fields.append(End())
    index = 0
    scopes[len(ind) + 1] = fields
    for f in fields:
        if f.index :
            raise LayoutError("Cannot use a field object more than once")
        f.index = ind + [index]
        pending_pointers = check_pending_pointers(pending_pointers, scopes)
        if isinstance(f, R):
            # continue below
            pattern(f.body, ind + [index], scopes, pending_pointers)
        elif isinstance(f, P):
            if (f.offset() == []):  # the offset has not yet been seen
                pending_pointers.append(f)
            elif (f.landing() == []):  # the landing has not yet been visited
                complete_pointer(f, scopes)
            else:  # the span has been visited (this should never execute, actually)
                pass
        index += 1


a_field = F()
a_pattern = [P(a_field, 3), F(), R([F(), F(), V(), a_field])]
print("ciaooo")
pattern(a_pattern)
a_pattern[0].landing()
    

