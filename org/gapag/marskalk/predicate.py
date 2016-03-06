
def __printindex(name, ls):
    return printFact("%s %s" % (name, str(ls[::-1]).replace(",","").replace("[","").replace("]","")))

def printindex(ls):
    return __printindex("index", ls)

def printoffset(ls):
    return __printindex("offset",ls)

def printUnknownLength(ls):
    return printFact("unknownLength"+printindex(ls))

def printlength( i):
    return printFact("span %s" % i)

def printFact( format):
    return "( %s )" % format

class Predicate:
    field = None

    def __init__(self, field):
        self.field = field

    def getindex(self):
        return self.field.getindex()
    
class Beg(Predicate):
    def __str__(self):
        return printFact("beg %s" % printindex(self.getindex()))

    def __init__(self, field):
        Predicate.__init__(self, field)


class Len(Predicate):
    def __str__(self):
        return printFact("len %s" % printindex(self.getindex()))

    def __init__(self, field):
        Predicate.__init__(self, field)


class Val(Predicate):
    def __str__(self):
        return printFact("val %s" % printindex(self.getindex()))

    def __init__(self, field):
        Predicate.__init__(self, field)


class RepLen(Predicate):
    def __str__(self):
        return printFact("val %s" % printindex(self.getindex()))

    def __init__(self, field):
        Predicate.__init__(self, field)

class Rep(Predicate):
    def __str__(self):
        return printFact("repeat %s %s" % 
                              (printindex(self.getindex()), 
                               printlength(len(self.field.body))))

    def __init__(self, field):
        Predicate.__init__(self, field)

class Pointer(Predicate):
    def __str__(self):
        return printFact("ptr %s %s %s" % 
                (printindex(self.field.getindex()), 
                 printoffset(self.field.offset()), printlength(self.field.span)))
        

    def __init__(self, field):
        Predicate.__init__(self, field)


