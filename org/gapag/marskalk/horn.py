from org.gapag.datastructures.hash_tree import *
import matplotlib.pyplot as plt
import networkx as nx

inference_graph = nx.DiGraph()

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
    
    def is_empty(self):
        return len(self.predicates)==0
    
    predicates = []
    hashes = {
        'Beg': HashTree(),
        # contains all beg.
        'Len': HashTree(),
        # contains all len.
        'Val': HashTree(),
        # contains all values.
        'Rep': HashTree(),
        # contains all repeat.
        'RepLen': HashTree(),
        # contains all replen
        'Pointer': HashTree()
    }

    def get_bin(self, item):
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

    def build_hash_trees(self, initial):
        for item in initial:
            insert(self.hashes[self.get_bin(item)], item.getindex(), item)
        self.predicates = self.predicates + initial# should never add duplicates...

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
    for kb in kbs:
        if pred in kb:
            return True


# side effect
def learn(kb_old, kb_new):
    kb_old.build_hash_trees(kb_new.predicates)

def premise_check(responsible_premise, other_premises, *kbs):
    concrete_premises = []
    for pr in other_premises:
        premise = pr(responsible_premise)
        concrete_premises.append(premise)
        if not known(premise, kbs):
            return None
    return concrete_premises


def create_consequences(responsible_premise, consequences):
    return [x(responsible_premise) for x in consequences]


def add_inferences(concrete_consequences, kb_old, kb_last_round, kb_round):
    inferred = []
    for consequence in concrete_consequences:
        if not known(consequence, kb_old,
                     kb_last_round):  # the consequence does not appear
            if not known(consequence, kb_round):
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
    concrete_premises = premise_check(responsible_premise, other_premises, kbs)
    if concrete_premises:
        all_premises = [responsible_premise]+concrete_premises
        concrete_consequences = create_consequences(responsible_premise,
                                                    consequences)
        inferred = add_inferences(concrete_consequences, kb_old, kb_last_round,
                                  kb_round)
        inference_graph.add_nodes_from(
            map(str,all_premises+inferred)
        )
        inference_graph.add_node(name)
        inference_graph.add_edges_from(
            [(k,name) for k in all_premises]+
            [(name,k) for k in inferred]
        )


def next_field(field, derive):
    """
    return the field that is inc fields far
    :param field: 
    :param inc: function computing the new identifier from the given one 
    :return: 
    """
    # creation of second consequence, this is included in a function
    new_field = None
    field_index = [x for x in field.getindex()]  # get i+1
    derive(field_index)
    fields = retrieve(field_hash, field_index)  # the field at index i+1
    if not fields:
        return None
    else:
        new_field = fields[-1]
    return new_field


def add_some(val):
    def add_val(x):
        x[-1] += val
        return x
    return add_val


def infer_forward(b, kb_old, kb_last_round, kb_round, *kbs):
    # creation of second consequence, this is included in a function

    i_fw_field = next_field(b.field, add_some(1))
    if not i_fw_field:
        return
    infer_generic("forward(" + str(b.getindex()) + ")",
                  b,
                  [lambda x: Len(x.field)],
                  kb_old,
                  kb_last_round,
                  kb_round,
                  [
                      lambda x: Val(x.field),
                      # TODO maybe not necessary to have lambdas
                      lambda x: Beg(i_fw_field)
                  ],
                  kbs
                  )


def infer_backward(b, kb_old, kb_last_round, kb_round, *kbs):
    # creation of second consequence, this is included in a function
    i_bw_field = next_field(b.field, add_some(-1))
    if not i_bw_field:
        return
    infer_generic("backward(" + str(b.getindex()) + ")",
                  b,
                  [lambda x: Len(i_bw_field)],
                  kb_old,
                  kb_last_round,
                  kb_round,
                  [
                      lambda x: Val(i_bw_field),
                      # TODO maybe not necessary to have lambdas
                      lambda x: Beg(i_bw_field)
                  ],
                  kbs
                  )


def infer_join(b, kb_old, kb_last_round, kb_round, *kbs):
    i_jo_field = next_field(b.field, add_some(1))
    if not i_jo_field:
        return
    infer_generic("join(" + str(b.getindex()) + ")",
                  b,
                  [lambda x: Beg(i_jo_field)],
                  kb_old,
                  kb_last_round,
                  kb_round,
                  [
                      lambda x: Len(x.field),
                      # TODO maybe not necessary to have lambdas
                  ],
                  kbs
                  )


def infer_jump_right(ptr, kb_old, kb_last_round, kb_round, *kbs):
    infer_generic("jump_right(" +
                  (",".join(
                      map(str,[
                        ptr.field.offset(),
                        ptr.field.landing(),
                        ptr.getindex()])
                  )) + ")",
                  ptr,
                  [
                      lambda x: Val(ptr.getindex())
                      , lambda x: Beg(ptr.field.offset())
                  ],
                  kb_old,
                  kb_last_round,
                  kb_round,
                  [
                      lambda x: Beg(ptr.field.landing())
                  ],
                  kbs
                  )


def infer_jump_left(ptr, kb_old, kb_last_round, kb_round, *kbs):
    infer_generic("jump_left(" +
                  (",".join(
                        map(str,
                            [
                                ptr.field.offset(),
                                ptr.field.landing(),
                                ptr.getindex()   
                            ])
                            )
                      ) + ")",
                  ptr,
                  [
                      lambda x: Val(ptr.getindex())
                      , lambda x: Beg(ptr.field.landing())
                  ],
                  kb_old,
                  kb_last_round,
                  kb_round,
                  [
                      lambda x: Beg(ptr.field.offset())
                  ],
                  kbs
                  )

def next_level(increment):
    def next_level_0(x):
        increment(x).append(0)
    return next_level_0

def infer_replen(rep, kb_old, kb_last_round, kb_round, *kbs):
    shifted = add_some(len(rep.field.body))
    same = add_some(0)
    end_begin = next_field(rep,shifted)
    below_start_begin = next_field(rep, next_level(same)) 
    below_end_begin = next_field(rep, next_level(shifted))
    if not (end_begin and below_end_begin and below_start_begin):
        return
    infer_generic("rep_len(" + str(rep.getindex()) + ")",
                    rep,
                    [
                        lambda x : Beg(shifted),
                        lambda x : Beg(rep.field)
                    ],
                    kb_old,
                    kb_last_round,
                    kb_round,
                    [
                        lambda x: RepLen(rep.field),
                        lambda x: Beg(below_start_begin),
                        lambda x: Beg(below_end_begin)
                    ],
                    kbs
                  )


def saturate(initial):
    initial_knowledge = KnowledgeFragment(initial)
    old = KnowledgeFragment()
    not_saturated = True
    while not_saturated :
        inferred = saturate_round(old, initial_knowledge)
        not_saturated = not inferred.is_empty()
        initial_knowledge = inferred
    return old
    

# Applies a reasoning round. Returns a new kb_new
def saturate_round(kb_old, kb_last_round):
    kb_round = KnowledgeFragment()
    # Informally: in a rule, the responsibility set is the set of predicates
    # occurring in the premises that identify the rule.
    # There might be more than one responsibility set. The most interesting ones
    # are those who are singletons.
    # For instance: {Beg} is responsible for forward, backwards, join
    #               {Len} is responsible for forward, backwards
    #              {Pointer} or {Val, Beg} is responsible for jumpRight and jumpLeft
    #              {Rep} for replen

    begins = (kb_last_round.begins(), kb_old.begins())
    pointers = (kb_last_round.pointers(), kb_old.pointers())
    reps = (kb_last_round.repeats(), kb_old.repeats())
    
    
    inference_funcs =[(infer_forward    , begins),
                      (infer_backward   , begins),
                      (infer_join       , begins),
                      (infer_jump_left  , pointers),
                      (infer_jump_right , pointers),
                      (infer_replen     , reps)]
    
    def apply_inference(inf_fun):
        for responsible in inf_fun[1][0]:
            inf_fun[0](responsible,kb_old, kb_last_round, kb_round, kb_old, kb_last_round)
        for responsible in inf_fun[1][1]:
            inf_fun[0](responsible,kb_old, kb_last_round, kb_round, kb_old)
    
    for func in inference_funcs  :
        apply_inference(func)
    
    learn(kb_old,kb_last_round)
    return kb_round

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

beginning = F()
layout = [beginning, F(), P(None,2), R([F(), P(None,2), V()])]
predicates = mu_labeling(layout)
predicates.append(Beg(beginning))
old = saturate(predicates)
print("cosa ora")