from dot_printer import *

class Rule :
    
    responsible_premise = None
    other_premises = None
    consequences = None
    name = None

    def __init__(self, name, premises, consequences):
        self._add_predicates(premises, consequences)
        
    def _add_predicates(self, premises, consequences):
        self.responsible_premise = premises[0]
        self.other_premises = premises[1:]
        self.consequences = consequences
    
    def __str__(self):
        return dot_friendly(\
            self.name+\
            str(self.responsible_premise)+ \
            "".join(map(str, self.other_premises))+ \
            "".join(map(str, self.consequences)))
            
        
class ForwardBackward (Rule):
    
    def __init__(self, name, premises, consequences):
        self.name = name
        self._add_predicates(premises, consequences)
        
class Join (Rule):
    def __init__(self, premises, consequences):
        self.name = "join"
        self._add_predicates(premises, consequences)
        
class Jump (Rule):
    def __init__(self, name, premises, consequences):
        self.name = "jump_"+name
        self._add_predicates(premises, consequences)
        
class RepLen (Rule):
    def __init__(self, premises, consequences):
        self.name = "repLen"
        self._add_predicates(premises, consequences)
        