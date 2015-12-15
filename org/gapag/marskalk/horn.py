from org.gapag.datastructures.hash_tree import *
from org.gapag.marskalk.field import *

class Predicate:
    field = None

    def __init__(self, field):
        self.field = field

    def getindex(self):
        return self.field.getindex()


class Beg(Predicate):
    def __str__(self):
        return "beg(" + str(self.field.getindex()) + ")"

    def __init__(self, field):
        Predicate.__init__(self, field)


class Len(Predicate):
    def __str__(self):
        return "len(" + str(self.field.getindex()) + ")"

    def __init__(self, field):
        Predicate.__init__(self, field)


class Val(Predicate):
    def __str__(self):
        return "val(" + self.field.getindex() + ")"

    def __init__(self, field):
        Predicate.__init__(self, field)


class RepLen(Predicate):
    def __str__(self):
        return "repLen(" + self.field.getindex() + ")"

    def __init__(self, field):
        Predicate.__init__(self, field)


class Rep(Predicate):
    def __str__(self):
        return "rep(" + str([self.field.getindex(), len(self.field.body)]) + ")"

    def __init__(self, field):
        Predicate.__init__(self, field)


class Pointer(Predicate):
    def __str__(self):
        return "ptr(" + str([self.field.getindex(), self.field.offset(),
                             self.field.landing()]) + ")"

    def __init__(self, field):
        Predicate.__init__(self, field)


class KnowledgeFragment:
    predicates = []
    hashes = {
        'Beg' : HashTree(),
        # contains all beg.
        'Len' : HashTree(),
    # contains all len.
        'Val' : HashTree(),
    # contains all values.
        'Rep': HashTree(),
    # contains all repeat.
        'RepLen' : HashTree(),
    # contains all replen
        'Pointer' : HashTree()
    }
    
    
    def get_bin(self,item):
        key = ""
        if isinstance(item, Beg):
            key = 'Beg'
        elif isinstance(item, Len):
            key = 'Len'
        elif isinstance(item, Val):
            key = 'Val'
        elif isinstance(item, Rep):
            key = 'Rep'
        elif isinstance(item, RepLen):
            key = 'RepLen'
        elif isinstance(item, Pointer):
            key = 'Pointer'
        return key
    
    def build_hash_trees(self,initial):
        for item in initial:
            insert(self.hashes[self.get_bin(item)], item.getindex(), item)
        self.initial = self.initial+initial 
        
    def insert(self, item):
        self.build_has_trees([item])
    
    def __contains__(self, item):
        rtr = retrieve(self.hashes[self.get_bin(item)], item.getindex())
        if rtr == None:
            return False
        else:
            return rtr[-1] == item 
        
    def __init__(self, initial=[]):
        self.build_hash_trees(initial)

    def begins(self):
        return filter(lambda x: isinstance(x, Beg), self.predicates)

    def lengths(self):
        return filter(lambda x: isinstance(x, Len), self.predicates)

    def values(self):
        return filter(lambda x: isinstance(x, Val), self.predicates)

    def pointers(self):
        return filter(lambda x: isinstance(x, Pointer), self.predicates)

    def repeats(self):
        return filter(lambda x: isinstance(x, Rep), self.predicates)

    def repeatLengths(self):
        return filter(lambda x: isinstance(x, RepLen), self.predicates)

def known(pred, *kbs):
    for kb in kbs :
        if pred in kb:
            return True


# side effect
def learn(kb_old, kb_new):
    kb_old.build_hash_trees(kb_new)
    

def infer_forward(b, kb_old, kb_last_round, kb_round,consequences, *kbs):
    """
    
    :param b: 
    :param kb_old: 
    :param kb_last_round: 
    :param kb_round: 
    :param kbs: List of knowledge fragments where Len can dwell 
    :return: 
    """
    fw_len = Len(b.field)
    if known(fw_len, kbs) : # check of second premise; further premises and-ed with known invocations
        # creation of first consequence, this is included in a function
        fw_val = Val(b.field) # create val(i)
        # creation of second consequence, this is included in a function
        i_plus_one = [x for x in b.getindex()] # get i+1
        i_plus_one[-1] += 1
        i_fw_field = retrieve(field_hash,i_plus_one) # the field at index i+1
        if i_fw_field :
            fw_beg = Beg(i_fw_field[-1]) # create Beg(i+1)
        
        
        # below here: check all the consequences being new or not. iterable
        # Idea is also that if same predicate is inferred by multiple rules,
        # this is signalled. TODO Beware, if fw_beg was previously inferred in the 
        # same round this is copied!
        if not known(fw_beg, kb_last_round, kb_old):
            # add fw_beg
            kb_round.insert(fw_beg)
        if not known(fw_val, kb_last_round, kb_old):
            # add fw_val
            kb_round.insert(fw_val)

def premise_check(responsible_premise, other_premises, *kbs) :
    for pr in other_premises:
        if not known(pr(responsible_premise.getindex()), kbs) :
            return False
    return True

def create_consequences(responsible_premise, consequences):
    return [x(responsible_premise) for x in consequences]

def add_inferences(concrete_consequences, kb_old, kb_last_round, kb_round):
    # should not add more than once something in kb_round;
    # if kb_round already contains what you are putting in it, TODO must remember this
    inferred = []
    for consequence in concrete_consequences:
        if not known(consequence, kb_old,kb_last_round):# the consequence does not appear
            if not known(consequence, kb_round) :
                kb_round.insert(consequence)
            inferred.append(consequence)
    return inferred

def infer_generic(name, 
                  responsible_premise, 
                  other_premises, 
                  kb_old, 
                  kb_last_round, 
                  kb_round, 
                  consequences, 
                  *kbs):
    """
    Apply single rule with given premises, and consequences.
    :param rule name
    :param responsible_premise: first premise of the rule 
    :param other_premises : list of functions taking first_premise as input, 
        computing the other premises
    :param kb_old: old knowledge fragment
    :param kb_last_round: knowledge fragment of predicates inferred in previous round
    :param kb_round: this round's inferences
    :param consequences: list of functions that create rhs predicates taking first_premise as input 
    :param kbs: list of knowledge fragments to be searched for other_premises
    :return: 
    """
    if premise_check(responsible_premise, other_premises, kbs):
        concrete_consequences = create_consequences(responsible_premise, consequences)
        inferred = add_inferences(concrete_consequences,kb_old,kb_last_round, kb_round)
    # TODO should save the rule in a graph. use NetworkX if needed
    # TODO rule name labels arches, premises and consequences name nodes

def infer_backward(b, kb_old, kb_last_round, kb_round, *kbs):
    fw_len = Len(b.field)
    if known(fw_len,kb_last_round, kb_old) : # if i know len(i)
        fw_val = Val(b.field) # create val(i)
        i_minus_one = [x for x in b.getindex()] # get i+1
        i_minus_one[-1] += 1
        i_fw_field = retrieve(field_hash,i_minus_one) # the field at index i+1
        if i_fw_field :
            fw_beg = Beg(i_fw_field[-1]) # create Beg(i+1)
            
        if not known(fw_beg, kb_last_round, kb_old):
            # add fw_beg
            kb_round.insert(fw_beg)
        if not known(fw_val, kb_last_round, kb_old):
            # add fw_val
            kb_round.insert(fw_val)

# Applies a reasoning round. Returns a new kb_new
def saturate_round(kb_old, kb_last_round):
    kb_round = KnowledgeFragment()
    begs = kb_last_round.begins()
    # Informally: in a rule, the responsibility set is the set of predicates
    # occurring in the premises that identify the rule.
    # There might be more than one responsibility set. The most interesting ones
    # are those who are singletons.
    # For instance: {Beg} is responsible for forward, backwards, join
    #               {Len} is responsible for forward, backwards
    #              {Pointer} or {Val, Beg} is responsible for jumpRight and jumpLeft
    #              {Rep} for replen
    
    # Forward N N
    # Forward N O
    # Forward O N
    for b in begs: # beg(i)
        infer_forward(b,kb_old, kb_last_round, kb_round, kb_old, kb_last_round)
        infer_backward(b,kb_old, kb_last_round, kb_round, kb_old, kb_last_round)
    for b in kb_old.begins() :
        infer_forward(b,kb_old, kb_last_round, kb_round, kb_last_round)
        infer_backward(b,kb_old, kb_last_round, kb_round, kb_last_round)
    
    
    
    # Join N N
    # Join N O
    # Join O N
    # JumpRight O O N
    # JumpRight O N N
    # JumpRight N O N
    # JumpRight N N N
    # JumpLeft O O N
    # JumpLeft O N N
    # JumpLeft N O N
    # JumpLeft N N N
    # RepLen O O N
    # RepLen O N O
    # RepLen O N N
    # RepLen N N O
    # RepLen N O N
    # RepLen N N N
    
    
    #Val
    # JumpRight O N O
    # JumpRight N N O
    # JumpLeft O N O
    # JumpLeft N N O
    
    #Len
    
    # Backward O N
    
    #Ptr
    #
    # JumpRight N O O
    # JumpLeft N O O

    # Rep
    # RepLen N O O
    