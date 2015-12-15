from horn import *
from org.gapag.datastructures.hash_tree import *

field_hash = HashTree()

class Field:
    
    index = []

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
        if not field:
            self.origin = self
        else:
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


def check_pending_pointers(pending_pointers, scopes, initial):
    filtered = []
    for f in pending_pointers:
        if f.offset():
            complete_pointer(f, scopes, initial)
        else:
            filtered.append(f)
    return filtered


def index_add(index, span, scopes):
    index_pos = index[-1]  # position of this field in its context
    context = scopes[len(index)]  # context of the field; a list of fields
    if len(context) > index_pos + span:
        new_index = [x for x in index]
        new_index[-1] = index_pos + span
        return new_index
    else:
        what_is_left = len(context) - index_pos-1
        span_left = span - what_is_left
        return index_add(index[:-1], span_left, scopes)


def complete_pointer(f, scopes, initial):
    if len(f.offset()) <= len(f.index):  # must point to same or outer scope
        # is the scope long enough?
        landing_index = index_add(f.offset(),f.span, scopes)
        f.land = scopes[len(landing_index)][landing_index[-1]] # look at an upper scope and compute the value of the landing pad
        initial.append(Pointer(f))
    else:  # Pointing to a field that is more nested
        raise PointerError('Pointing to a more nested field')


class LayoutError(Exception):
    pass


def mu_labeling(fields, ind=[], scopes={},
                pending_pointers=[], initial=[]):  # linearized=[]
    fields.append(End())
    index = 0
    scopes[len(ind) + 1] = fields
    for f in fields:
        if f.index:
            raise LayoutError("Cannot use a field object more than once")
        f.index = ind + [index]
        pending_pointers = check_pending_pointers(pending_pointers, scopes, initial)
        # Case REPEAT
        if isinstance(f, R):
            # continue below
            initial.append(Rep(f))
            mu_labeling(f.body, ind + [index], scopes, pending_pointers, initial)
        # Case POINTER
        elif isinstance(f, P):
            initial.append(Len(f))
            if (f.offset() == []):  # the offset has not yet been seen
                pending_pointers.append(f)
            elif (f.landing() == []):  # the landing has not yet been visited
                complete_pointer(f, scopes, initial)
            else:  # the span has been visited (this should never execute, actually)
                pass
        # Case FIELD : knows length
        elif isinstance(f,F):
            initial.append(Len(f))
        # Case VARFIELD: does nothing
        elif isinstance(f,V):
            pass
            
        insert(field_hash,f.getindex(),f)
        index += 1
    return initial
