import argparse
import subprocess
from hash_tree import *
from predicate import Len, Beg, Val, Rep, Pointer
from pyparsing import *
import predicate
import copy

engine = """
(deftemplate beg
  "Beginning of an item"
  (multislot index
    (type INTEGER)
    (default  0 )
    )
)

(deftemplate len
  "Length of an item"
  (multislot index
    (type INTEGER)
    (default  0 )
    )
)

(deftemplate replen
  "Length of repetition"
  (multislot index
    (type INTEGER)
    (default  0 )
    )
)

(deftemplate val
  "value of an item"
  (multislot index
    (type INTEGER)
    (default  0 )
    )
)

(deftemplate ptr
  "Pointer"
  (multislot index
         (type INTEGER)
         (default 0))
  (multislot offset
         (type INTEGER)
         (default 0))
  (slot span
         (type INTEGER)
         (default 0))
)

(deftemplate repeat
  "Repeat item"
  (multislot index
         (type INTEGER)
         (default 0))
    (slot span
         (type INTEGER)
         (default 0))
)
           

(defrule read-and-forward
  (beg (index ?id $?rest))
  (len (index ?id $?rest))
  =>
  (assert (val (index ?id ?rest)))
  (assert (beg (index (+ ?id 1) ?rest)))
)

(defrule join
  (beg (index ?id $?rest))
  (beg (index ?oid&:(= ?oid (+ ?id 1)) $?rest))
  =>
  (assert (len (index ?id ?rest)))
)

(defrule backward  
  (len (index ?id $?rest))
  (beg (index ?oid&:(= ?oid (+ ?id 1)) $?rest))
  =>
  (assert (beg (index ?id ?rest)))
)


(defrule count-right
  (ptr (offset ?ptrhead $?tail) (span ?l) (index $?label))
  (val (index $?label))
  (beg (index ?ptrhead $?tail))
  =>
  (assert (beg (index (+ ?ptrhead ?l) ?tail)))
)

(defrule count-left
  (ptr (offset ?ptrhead $?tail) (span ?l) (index  $?label))
  (val (index $?label))
  (beg (index ?q&:(= ?q (+ ?ptrhead ?l)) $?tail))
  =>
  (assert (beg (index ?ptrhead $?tail)))
)

(defrule enter-repeat
  (repeat (index ?a $?rest )(span ?len) )
  (beg (index ?a $?rest))
  (beg (index ?q&:(= ?q (+ ?a 1)) $?rest))
  =>
  (assert (beg  (index 0 ?a ?rest)))
  (assert (beg (index ?len ?a ?rest)))
  (assert (replen (index ?a $?rest)))
)


(deffacts initial-knowledge "Test"
  (beg (index 0))
  (len (index 0))
)

(deftemplate unknownLength
  "unknown length item"
  (multislot index
    (type INTEGER)
    (default  0 )
    )
)

(defrule check-all-variable-lengths-are-found
  (unknownLength (index $?s))
  (not (len (index $?s)))
  =>
  (assert (variable-not-found))
)

(defrule check-all-repeats-have-length
  (unknownLength (index $?s))
  (repeat (index $?s) )
  (not (replen (index $?s)))
  =>
  (assert (repeat-not-bounded))
)

(deffunction test-all-unknown-lengths-were-found ()
  (if
      (any-factp ((?vv variable-not-found)) (eq 1 1));?first:index
      then
    FALSE
    else
    TRUE
    )
  )

(deffunction test-all-repeats-were-bounded ()
      (if
      (any-factp ((?rep repeat-not-bounded)) (= 1 1))
       then FALSE
       else TRUE
      )
)

(retract *)
"""

epilogue = """
(run)
(if ( test-all-unknown-lengths-were-found ) then
(printout t "1" crlf) else
(printout t "0" crlf))

(if ( test-all-repeats-were-bounded ) then
(printout t "1" crlf) else
(printout t "0" crlf))
(facts)
(exit)
"""

class HornBinDeserializationParser:
    def __init__(self):
        self.unknownLengths = []
        self.nameDict = {}
        self.depends = {}
        self.layout = []
        self.scopes = []
        self.scopes.append(self.layout)
    
    def levelDown(self, pred):
        newLayout = []
        self.scopes.append(newLayout)
        self.layout = newLayout
        
    def levelUp(self, ob):
        popped = self.scopes.pop()
        self.layout = self.scopes[-1]
        
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
                    # todo: if 
                elif key=='v':
                    ob = pred.v
                    fi = V()
                    self.unknownLengths.append(fi)
                elif key=='f':
                    ob = pred.f
                    fi = F()
                    # adds a F() and adds itself if has an id
                elif key=='r':
                    ob = pred.r
                    body = self.levelUp(ob)
                    fi = R(body)
                    self.unknownLengths.append(fi)
                else:
                    ob = {}
                try :
                    identity = ob['id'][0]
                    if key == 'p' and identity == fi[1]:
                        fi = fi[0]
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
        return (self.s("(")+ (self.identifier()("offset")) +self.s("->")
                    + Word(nums)("span") 
                +self.s(")")+self.identDef())("p")
    
    def repetition(self):
        rep = Forward()
        rep << ((self.s("[").addParseAction(self.levelDown)+ OneOrMore(self.anyField(rep).setParseAction(self.addToLayout)) +self.s("]"))
                +self.s("*")+Optional(self.identDef()))
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
                    # If pointer points to other pointer, unpack it from tuple.
                    if isinstance(fi[0].origin, tuple):
                        fi[0].origin = fi[0].origin[0]
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

syntax_help= """
Description of layout syntax: 
  f                    : a fixed length field
  v                    : a variable length field 
  ( <any word> -> N )  : a pointer field with origin <any word> spanning over N
    fields
  [...other fields...]*: repetition field.
  
All the above fields can be annotated with an angular bracketed identifier 
to be referenced by pointer fields.
EXAMPLES:
  f(<me> -> 1)[f]<me>*
  fvff
  vff

Spaces can be inserted wherever according to your taste. Parentheses indicate
pointer fields, so you cannot use them to separate the fields.
  
  f<me> (<me> -> 3) v (<I> -> 1) v<I> f
  f (<me> -> 3)<me> v v<var> (<var> -> 1)
  

Notice that the identifier for repetition fields occurs between the closing
bracket and the asterisk.
  [ (<var> -> 1) v<var> (<varr> -> 2)<varr> v ]*<repid>
  f [ (<var> -> 1) v<var> (<varr> -> 2)<varr> v ]*<repid>
  f (<repid> -> 1)[ (<var> -> 1) v<var> (<varr> -> 2)<varr> v ]*<repid>
"""

def arguments():
    parser = argparse.ArgumentParser(description='Horn Binary deserialization.')
    parser.add_argument('--syntax', action="store_true", help='prints syntax help and exits')
    parser.add_argument('-l', type=str,help="Inline layout definition", default="")
    parser.add_argument('-i', type=str, help='Input file')
    parser.add_argument('-o', type=str, help='output file', default='output.clp')
    return parser.parse_args()

if __name__ == "__main__":
    args = arguments()
    pp = HornBinDeserializationParser()
    if args.syntax:
        print syntax_help
        exit(0)
    if args.i:
        # read from file
        with open(args.i,'r') as f:
            spec = f.read()
    if args.l:
        spec = args.l
    if not (args.l or args.i):
        print "No input given."
        exit(0)
    out = args.o
    if not out:
        out = "output.clp"
    
    layout = pp.parsedef(spec)
    # if layout starts with a repetition or a varfield, reject immediately.
    if not layout or layout == []:
        print "Empty layout."
        exit(0)
    if isinstance(layout[0],(R,V)):
        print "A layout starting with a v or []* cannot be deserialized"
        exit(0)
    field_hash = HashTree()
    predicates = mu_labeling(layout)
    predicates.append(Beg(layout[0]))
    clipsPreds = ""
    for c in predicates:
        clipsPreds += '\n'+str(c)
     
    initialKnowledge = predicate.printFact('deffacts inp "%s %s" %s' % ("kb for", spec, clipsPreds))
    initialize = "(watch activations)\n(watch facts)\n(reset)\n(run)\n"
    unknowns = ""
    if len(pp.unknownLengths) > 0:
        for v in pp.unknownLengths:
            unknowns += '\n'+predicate.printUnknownLength(v.getindex())
        unknowns = predicate.printFact("assert "+unknowns)
    with open(out,'w') as f:
        f.write(engine+initialKnowledge+initialize+unknowns+epilogue)
    with open("boot.clp",'w') as f:
        f.write("(batch %s)\n"%out)
    result = subprocess.check_output(["clips","-f","boot.clp"])
    with open("result.out", 'w') as f:
        f.write(result)
    for k in reversed(result.split("\n")):
        if k == "CLIPS> (facts)":
            break
        else:
            if "variable-not-found" in k:
                print "Not deserializable: the length of a varfield was not computed."
            elif "repeat-not-bounded" in k:
                print "Not deserializable: a repeat field was not bounded."
    print "Check result.out for the clips output and more detailled information."