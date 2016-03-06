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
    
    def __printindex(self, name, ls):
        return self.printFact("%s %s" % (name, str(ls[::-1]).replace(",","").replace("[","").replace("]","")))
    
    def printindex(self, ls):
        return self.__printindex("index", ls)

    def printoffset(self, ls):
        return self.__printindex("offset",ls)

    def printlength(self, i):
        return self.printFact("span %s" % i)
    
    def printFact(self, format):
        return "( %s )" % format

class Beg(Predicate):
    def __str__(self):
        return self.printFact("beg %s" % self.printindex(self.getindex()))

    def __init__(self, field):
        Predicate.__init__(self, field)


class Len(Predicate):
    def __str__(self):
        return self.printFact("len %s" % self.printindex(self.getindex()))

    def __init__(self, field):
        Predicate.__init__(self, field)


class Val(Predicate):
    def __str__(self):
        return self.printFact("val %s" % self.printindex(self.getindex()))

    def __init__(self, field):
        Predicate.__init__(self, field)


class RepLen(Predicate):
    def __str__(self):
        return self.printFact("val %s" % self.printindex(self.getindex()))

    def __init__(self, field):
        Predicate.__init__(self, field)

class Rep(Predicate):
    def __str__(self):
        return self.printFact("repeat %s %s" % 
                              (self.printindex(self.getindex()), 
                               self.printlength(len(self.field.body))))

    def __init__(self, field):
        Predicate.__init__(self, field)

class Pointer(Predicate):
    def __str__(self):
        return self.printFact("ptr %s %s %s" % 
                (self.printindex(self.field.getindex()), 
                 self.printoffset(self.field.offset()), self.printlength(self.field.span)))
        

    def __init__(self, field):
        Predicate.__init__(self, field)


