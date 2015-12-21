from org.gapag.datastructures.hash_tree import *

try:
    import matplotlib.pyplot as plt
except:
    raise
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
        return "val(" + str(self.field.getindex()) + ")"

    def __init__(self, field):
        Predicate.__init__(self, field)


class RepLen(Predicate):
    def __str__(self):
        return "repLen(" + str(self.field.getindex()) + ")"

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
        self.build_hash_trees([item])

    def __contains__(self, item):
        rtr = retrieve(self.hashes[self.get_bin(item)], item.getindex())
        if not rtr or not rtr[-1]:
            return False
        else:
            return rtr[-1].field == item.field

    def __str__(self):
        return str(map(str, self.predicates))

    def __init__(self, initial=None):
        if not initial:
            initial = []
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


def known(pred, kbs):
    for kb in kbs:
        if pred in kb:
            return True


# side effect
def learn(kb_old, kb_new):
    kb_old.build_hash_trees(kb_new.predicates)


def premise_check(responsible_premise, other_premises, kbs):
    concrete_premises = []
    for pr in other_premises:
        premise = pr(responsible_premise)
        concrete_premises.append(premise)
        if not known(premise, kbs):
            return None
    return concrete_premises


def create_consequences(responsible_premise, consequences):
    return [x(responsible_premise) for x in consequences]


def add_inferences(responsible_premise, concrete_consequences, kb_old,
                   kb_last_round, kb_round, name, jumps):
    inferred = []
    messages = []
    for consequence in concrete_consequences:

        known_in_earlier_rounds = known(consequence, [kb_old, kb_last_round])
        known_in_this_round = known(consequence, [kb_round])
        if not known_in_earlier_rounds:  # the consequence does not appear
            if not known_in_this_round:
                kb_round.insert(consequence)
                messages.append("  discovering " + str(consequence))
            inferred.append(consequence)
            if name[0:4] == 'jump':
                jumps[name] = None
        else:  # idea is that a jump is to be remembered whenever it hops over unknown fields,
            # even if the consequences are known.
            # Jump should be done once, 
            if name[0:4] == 'jump':
                if name not in jumps:  # I never applied this jump.                    
                    opposite = name.replace('left', 'right')
                    if opposite == name:  # if nothing changed, redo the opposite
                        opposite = name.replace('right', 'left')
                    if opposite not in jumps:  # I never applied neither its opposite.
                        # Check if there are unknown values
                        # responsible_premise holds the two extremes of the jump
                        offset = responsible_premise.field.offset()
                        landing = responsible_premise.field.landing()
                        known_values = between(kb_last_round.hashes['Len'],
                                               offset, landing) \
                                       + between(kb_old.hashes['Len'], offset,
                                                 landing)
                        fields_between = filter(lambda x: isinstance(x, End),
                                                between(field_hash, offset,
                                                        landing))
                        if len(known_values) != len(fields_between):
                            jumps[name] = None  ## I am using jumps as a set
                            inferred.append(consequence)
                            messages.append("  implying " + str(consequence))
    if messages:
        print("\n".join([name + " applies,"] + messages))
    return inferred



def infer_generic(name,
                  iteration,
                  responsible_premise,
                  other_premises,
                  kb_old,
                  kb_last_round,
                  kb_round,
                  consequences,
                  kbs,
                  jumps={}):
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
        inferred = add_inferences(responsible_premise, concrete_consequences,
                                  kb_old, kb_last_round,
                                  kb_round, name, jumps)
        if not inferred:
            return
        inferred_nodes = map(str, inferred)
        premises_nodes = map(str, all_premises)
        predicate_nodes = inferred_nodes + premises_nodes
        rule_nodes = [(k, name) for k in premises_nodes] + \
                     [(name, k) for k in inferred_nodes]
        inference_graph.add_nodes_from(predicate_nodes, kind='predicate')
        inference_graph.add_node(name, kind='rule', label=iteration)
        inference_graph.add_edges_from(rule_nodes)


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


def infer_forward(iteration, b, kb_old, kb_last_round, kb_round, kbs):
    # creation of second consequence, this is included in a function

    i_fw_field = next_field(b.field, add_some(1))
    if not i_fw_field:
        return
    infer_generic("forward(" + str(b.getindex()) + ")",
                  iteration,
                  b,
                  [lambda x: Len(x.field)],
                  kb_old,
                  kb_last_round,
                  kb_round,
                  [
                      lambda x: Val(x.field),
                      lambda x: Beg(i_fw_field)
                  ],
                  kbs
                  )


def infer_backward(iteration, b, kb_old, kb_last_round, kb_round, kbs):
    # creation of second consequence, this is included in a function
    i_bw_field = next_field(b.field, add_some(-1))
    if not i_bw_field:
        return
    infer_generic("backward(" + str(b.getindex()) + ")",
                  iteration,
                  b,
                  [lambda x: Len(i_bw_field)],
                  kb_old,
                  kb_last_round,
                  kb_round,
                  [
                      lambda x: Val(i_bw_field),
                      lambda x: Beg(i_bw_field)
                  ],
                  kbs
                  )


def infer_join(iteration, b, kb_old, kb_last_round, kb_round, kbs):
    i_jo_field = next_field(b.field, add_some(1))
    if not i_jo_field:
        return
    infer_generic("join(" + str(b.getindex()) + ")",
                  iteration,
                  b,
                  [lambda x: Beg(i_jo_field)],
                  kb_old,
                  kb_last_round,
                  kb_round,
                  [
                      lambda x: Len(x.field),
                  ],
                  kbs
                  )


def infer_jump_right(iteration, ptr, kb_old, kb_last_round, kb_round, kbs):
    infer_generic("jump_right(" +
                  (",".join(
                      map(str,[
                        ptr.field.offset(),
                        ptr.field.landing(),
                        ptr.getindex()])
                  )) + ")",
                  iteration,
                  ptr,
                  [
                      lambda x: Val(ptr.field)
                      , lambda x: Beg(ptr.field.origin)
                  ],
                  kb_old,
                  kb_last_round,
                  kb_round,
                  [
                      lambda x: Beg(ptr.field.land)
                  ],
                  kbs
                  )


def infer_jump_left(iteration, ptr, kb_old, kb_last_round, kb_round, kbs):
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
                  iteration,
                  ptr,
                  [
                      lambda x: Val(ptr.field)
                      , lambda x: Beg(ptr.field.land)
                  ],
                  kb_old,
                  kb_last_round,
                  kb_round,
                  [
                      lambda x: Beg(ptr.field.origin)
                  ],
                  kbs
                  )

def next_level(increment):
    def next_level_0(x):
        increment(x).append(0)
    return next_level_0


def infer_replen(iteration, rep, kb_old, kb_last_round, kb_round, kbs):
    shifted = add_some(len(rep.field.body))
    same = add_some(0)
    end_begin = next_field(rep,shifted)
    below_start_begin = next_field(rep, next_level(same)) 
    below_end_begin = next_field(rep, next_level(shifted))
    if not (end_begin and below_end_begin and below_start_begin):
        return
    infer_generic("rep_len(" + str(rep.getindex()) + ")",
                  iteration,
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
    round_counter = 0
    initial_knowledge = KnowledgeFragment(initial)
    old = KnowledgeFragment()
    not_saturated = True
    while not_saturated :
        inferred = saturate_round(round_counter, old, initial_knowledge)
        not_saturated = not inferred.is_empty()
        initial_knowledge = inferred
        round_counter += 1
    return old


# Applies a reasoning round. Returns a new kb_new
def saturate_round(round_counter, kb_old, kb_last_round):
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
                      (infer_jump_left, pointers),
                      (infer_jump_right , pointers),
                      (infer_replen     , reps)]
    print("** In round **" + str(round_counter))
    def apply_inference(inf_fun):
        for responsible in inf_fun[1][0]:
            inf_fun[0](round_counter, responsible, kb_old, kb_last_round,
                       kb_round, [kb_old, kb_last_round])
        for responsible in inf_fun[1][1]:
            inf_fun[0](round_counter, responsible, kb_old, kb_last_round,
                       kb_round, [kb_old])
    
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
layout = [beginning, P(None, 3), P(None, 2), V()]


predicates = mu_labeling(layout)
predicates.append(Beg(beginning))
predicates_nodes = map(str, predicates)
inference_graph.add_nodes_from(predicates_nodes, kind='initial')
print(predicates_nodes)
initial_nodes = [u for (u, d) in inference_graph.nodes(data=True) if
                 d['kind'] == 'initial']
 
old = saturate(predicates)

pos = nx.pydot_layout(inference_graph)  # positions for all nodes

rul_nodes = [(u, d) for (u, d) in inference_graph.nodes(data=True) if
             d['kind'] == 'rule']
label_dict = {}
for (u, d) in rul_nodes:
    label_dict[u] = d['label']
rul_nodes = [list(l) for l in zip(*rul_nodes)][0]
pred_nodes = [u for (u, d) in inference_graph.nodes(data=True) if
              d['kind'] == 'predicate']

# nodes
nx.draw_networkx_nodes(inference_graph, pos, node_size=70, nodelist=rul_nodes)
nx.draw_networkx_nodes(inference_graph, pos, node_size=70, node_color='yellow',
                       nodelist=pred_nodes)
nx.draw_networkx_nodes(inference_graph, pos, node_size=70, node_color='blue',
                       nodelist=initial_nodes)

# edges
nx.draw_networkx_edges(inference_graph, pos,
                       width=1)
# labels
nx.draw_networkx_labels(inference_graph, pos, labels=label_dict,
                        font_color='yellow', font_size=30,
                        font_family='sans-serif')
nx.draw_networkx_labels(inference_graph, pos, font_size=20,
                        font_family='sans-serif')

plt.axis('off')
# plt.savefig("weighted_graph.png") # save as png
# plt.show() # display
