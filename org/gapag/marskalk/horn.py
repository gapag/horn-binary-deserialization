import os

from org.gapag.datastructures.hash_tree import *
from org.gapag.marskalk.predicate import Len, Beg, Val, Rep, Pointer
import clips
from pyparsing import *
import copy

class HornBinDeserializationParser:
    def __init__(self):
        self.nameDict = {}
        self.depends = {}
        self.layout = []
        self.scopes = []
        self.scopes.append(self.layout)
    
    def levelDown(self, pred):
        print "going down"
        newLayout = []
        self.scopes.append(newLayout)
        self.layout = newLayout
        
    def levelUp(self, ob):
        print "going up"
        popped = self.scopes.pop()
        self.layout = self.scopes[-1]
        try:
            id = ob['id']
            self.depends[id] = popped[1] # this depends stinks. What about more nested ids?
        except KeyError:
            pass
        return popped
    
    def addToLayout(self, *args):
        pred = args[-1]
        for key in ['r','p','f','v']:
            try:
                ob = pred[key]
                if key=='p':
                    ob = pred.p
                    refers = ob.offset[0]
                    fi = (P(None,ob.span), refers)
                    # adds a pair (Ptr, name of the label) and itself if has an id 
                elif key=='v':
                    ob = pred.v
                    fi = V()
                    # adds a V() and it adds itself to the dictionary if it has an id
                elif key=='f':
                    ob = pred.f
                    fi = F()
                    # adds a F() and adds itself if has an id
                elif key=='r':
                    ob = pred.r
                    body = self.levelUp(ob)
                    fi = R(body)
                else:
                    ob = {}
                try :
                    identity = ob['id'][0]
                    self.addToDict(identity, fi)
                except KeyError:
                    identity = ''
                    pass
                finally:
                    self.layout.append((identity, fi))
                return fi                
            except KeyError:
                pass
        return None
    def addToDict(self, label, fi):
        if self.nameDict.has_key(label):
            raise LayoutError("Cannot use %s more than once."%label)
        else:
            self.nameDict[label] = fi
    
    def parser(self):
        return OneOrMore((self.field() | self.varfield() |self.pointer() | self.repetition()).setParseAction(self.addToLayout))
    
    def s(self, what):
        return Suppress(what)
    
    def identifier(self):
        return self.s("<")+ Word(alphas)+self.s(">")
    
    def identDef(self):
        return Optional(self.identifier()("id"))
    
    def absField(self,l):
        return (Literal(l) + 
                Optional(self.identDef()))
    
    def field(self):
        return self.absField("f")("f") 
    
    def varfield(self):
        return self.absField("v")("v")
    
    def pointer(self):
        return (self.s("(|")+ (self.identifier()("offset")) +self.s("|>")
                    + Word(nums)("span") 
                +self.s("|)")+self.identDef())("p")
    
    def repetition(self):
        rep = Forward()
        rep << ((self.s("[").addParseAction(self.levelDown)+ OneOrMore(self.anyField(rep).setParseAction(self.addToLayout)) +self.s("]"))
                +Optional(self.identDef())+self.s("*"))
        return rep("r")
    
    def  anyField(self, f):
        return self.field() | self.varfield() | self.pointer() | f
    
    def __duplicateAllRepeats(self):
        for (id, item) in self.layout:
            if isinstance(item, R):
                self.__duplicateRepeat(item)
    
    def __duplicateRepeat(self, repeat):
        childrenStack = []
        # first, make a deep copy of this repeat
        dupe = copy.deepcopy(repeat.body)
        # make a dictionary label-object of this level
        dupeDict = dict(dupe)
        for (idx, (id, ob)) in enumerate(dupe):
            if isinstance(ob, R):
                # if there is a repeat, it needs to be duped too.
                childrenStack.append((idx, id, ob))
                pass
            elif isinstance(ob, tuple):
                refers = ob[1]
                try:
                    newObj = dupeDict[refers]
                    newKey = '1_'+refers
                    self.nameDict[newKey] = newObj
                    dupe[idx] = (id,(ob[0],newKey))
                    objInd = dupe.index((refers,newObj))
                    dupe[objInd] = (newKey, newObj)
                except Exception as e:
                    # ptr does not point to an obj at the same level, no need to
                    # dupe the key
                    print e
                    pass
        repeat.body = dupe + repeat.body
        # take care of other repetitions, replacing them in the duped half.
        for (idx, id, ob) in childrenStack:
            newRepeat = self.__duplicateRepeat(ob)
            repeat.body[idx] = (id, newRepeat)
        return repeat
    
    def parsedef(self, str):
        self.parser().parseString(str)
        self.__duplicateAllRepeats()
        self.__initPointers(pp.layout)
        return self.layout
        
    def __initPointers(self, l):
        for idx, (la, fi) in enumerate(l):
            if isinstance(fi, tuple):
                try:
                    wl = fi[1]
                    fi[0].origin = self.nameDict[wl]
                    fi = fi[0]
                except KeyError: 
                    raise LayoutError("invalid reference to non-existent field %s" % wl)
            elif isinstance(fi, R):
                self.__initPointers(fi.body)
            l[idx] = fi

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
        self.span = int(s)

    def offset(self):
        return self.origin.getindex()

    def landing(self):
        return self.land.getindex()

class PointerError(Exception):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return repr(self.value)

def mu_labeling(fields, ind=[], scopes={},
                pending_pointers=[], initial=[]):
    fields.append(End())

    scopes[len(ind) + 1] = fields
    for idx, f in enumerate(fields):
        if f.index != []:
            raise LayoutError("Cannot use a field object more than once")
        f.index = ind + [idx]
        pending_pointers = check_pending_pointers(pending_pointers, scopes, initial)
        # Case REPEAT
        if isinstance(f, R):
            # continue below
            initial.append(Rep(f))
            mu_labeling(f.body, ind + [idx], scopes, pending_pointers, initial)
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
    return initial

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
        new_index = index[:]
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

field_hash = HashTree()


pp = HornBinDeserializationParser()
layout = pp.parsedef("[v<caputo>(| <caputo> |> 1|)]*")
predicates = mu_labeling(layout)
predicates.append(Beg(layout[0]))

for pre in predicates:
    print pre
print os.getcwd()

# 
# clips.Load("clips.clp")
# clips.Reset()
# 
# tmp = clips.FindTemplate("beg")
# print tmp.PPForm()
# f1 = clips.Fact(tmp)
# f1_slotkeys = f1.Slots.keys()
# print f1_slotkeys
# print "please print this"
# print "print this other"
# print "print this gfeghtrhtrsh"
# print f1.PPForm()
# print "and this"


# clips.Reset()
# t0 = clips.BuildTemplate("person", """
#     (slot name (type STRING))
#     (slot age (type INTEGER))
# """, "template for a person")
# print t0.PPForm()
# f1 = clips.Fact(t0)
# f1_slotkeys = f1.Slots.keys()
# print f1_slotkeys
# 
# f1.Slots['name'] = "Grace"
# f1.Slots['age'] = 24
# print f1.PPForm()

# facts = """( beg (index 0) )
# ( len  ( index  0 ))
# ( ptr (label  0 ) (length  3 ) (index  0  ))
# ( len  ( index  0 1 ))
# ( len  ( index  1 1 ))
# ( len  ( index  2 1 ))
# ( len  ( index  3 1 ))
# ( repeat ( index  1 ) (length  4 ))
# ( len  ( index  2 ))
# """
# ff =  clips.BuildDeffacts("ripSem1_nocount", facts, "initial kb")
# clips.Reset()
# clips.Run()


#print predicates_nodes
