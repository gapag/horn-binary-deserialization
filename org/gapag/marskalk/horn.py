from org.gapag.datastructures.hash_tree import *

from rules import *
from predicate import *
from heapq import *

try:
    import matplotlib.pyplot as plt
except:
    raise
import networkx as nx

inference_graph = nx.DiGraph()

# prints to dot
dot_printer = DotPrinter()

class ApplicationRound :
    jumps={}
    def __init__(self):
        self.forward = False
        self.backward = False
        self.applied = {}
    
    def has_forward(self):
        return self.forward

    def has_backward(self):
        return self.backward
    
    ## Tells if the passed jump rule (or its opposite) has been applied.
    def has_jumped(self, jump_rule):
        s = str(jump_rule)
        opposite = s.replace('right','left')
        if s == opposite:
            opposite = s.replace('left','right')
        return self.jumps.has_key(opposite) or self.jumps.has_key(s)
    
    ## adds the passed rule to the set of rules that have been applied
    def was_applied(self, rule, cost_model):
        # Remember that a forward or a backward has been applied.
        if isinstance(rule, ForwardBackward):
            if rule.name == 'forward':
                self.forward = True
                cost_model.go_forward(rule)
            elif rule.name == 'backward':
                self.backward = True
                cost_model.go_backward(rule)
        if isinstance(rule, Jump):
            # this has indeed been applied
            cost_model.go_jumping(rule)
            self.jumps[str(rule)] = rule
        # remember the name of the applied rule.
        self.applied[str(rule)] = rule

class CostModel:
    # current positions are related to the Beg predicates found so far.
    # Generally a current position can be either an index,
    # or two indexes (which identify a buffered portion)
    # Application of a forward *might* increase (or decrease) the buffer
    # A right jump creates a buffering (if it does not exist yet)
    # A left jump is done only when a buffering exists
    # A backward can remove buffering (and leave with only one position)
    # A join and a replen have no effect (and both are applied only when there 
    # is some buffering)
    
    pending_right_jumps = []
    pending_left_jumps = []
    
    def go_forward(self, rule):
        field = rule.responsible_premise.field
        n_field = rule.consequences[-1].field
        if field.getindex() == self.current_position[0].getindex():
            self.current_position[0] = n_field
        if field.getindex() == self.current_position[1].getindex():
            self.current_position[1] = n_field
    
    def go_backward(self, rule):
        field = rule.responsible_premise.field
        p_field = rule.consequences[-1].field
        if field.getindex() == p_field.getindex():
            self.current_position[1] = p_field
            
    def go_jumping(self, rule):
        # if jumped right, expand span right
        # if jumped left, do nothing
        pass
    
    def within_current_position(self, index):
        return self.current_position[0].getindex() <= index <= self.current_position[1].getindex()
    
    def keep_in_memory_contribution(self,field):
        index = field.getindex()
        if self.within_current_position(index):
            return 0 ## WARNING : This means that any pointer found and used within the buffer is equivalent.
        else:
            left_b = self.current_position[0].getindex()
            right_b = self.current_position[1].getindex()
            btw = []
            if  index < left_b:
                btw = between(field_hash,left_b, index)
            elif index > right_b : 
                btw = between(field_hash,right_b, index)
            return len(btw)
        
    def estimate_right_jump(self, rule, kbs):
        # requirements: best jump is the jump that
        # a) results in the least bufferization (here the current position should play a role)
        # b) pointer is to be kept in memory the least possible number of rounds
        # Note that this does not give a deterministic choice.
        # TODO Study the various configurations that might arise. It seems 
        # no optimal method exists.
        #
        #
        
        #1 compute the number of elements spanned by the pointer
        pointer_field = rule.other_premises[0].field
        launch_field = rule.other_premises[1].field.getindex()
        landing_field = rule.consequences[0].field.getindex()
        all_fields = between(field_hash,launch_field,landing_field)
        right_jump_cost = len(all_fields)
        #2 compute how many of them are unknown
        unknowns = 0
        for kb_i in kbs:
            all_values = between(kb_i['Val'], launch_field, landing_field)
            unknowns += len(all_values)
        right_jump_cost += unknowns
        # Is the pointer outside the current position?
        right_jump_cost += self.keep_in_memory_contribution(pointer_field)
        return right_jump_cost
    
    def estimate_left_jump(self, rule, kbs):
        pass
    
    def __init__(self, init_field):
        self.current_position = [init_field, init_field] 
    
    def cost(self, rule, applied, kbs):
        if isinstance(rule, ForwardBackward):
            return rule
        elif isinstance(rule, Join):
            return rule
        elif isinstance(rule, Jump):
            ru = rule
            # 1) If I jumped right, DO NOT jump left 
            # 4) The latest I jump right, the better.
            # 5) Do not jump right if you can go forward. (==> do not jump right if you made a forward)
            if(rule.name == 'jump_right'):
                if applied.has_forward() :
                    ru = None
                cost = cost_model.estimate_right_jump(rule, kbs)
                heappush(self.pending_right_jumps,(cost, rule))
                 
            # 1) If I jumped left, DO NOT jump right
            # 3) The earlier I jump left, the better.
            # 6) Do not jump left if you can go backward (==> do not jump left if you made a backward).        
            elif rule.name == 'jump_left':
                if applied.has_backward():
                    ru = None
                cost = cost_model.estimate_left_jump(rule, kbs)
                heappush(self.pending_left_jumps,(cost, rule)) 
            if applied.has_jumped(rule):
                ru = None
            return ru
        elif isinstance(rule, RepLen):
            return rule



# A knowledge base.
class KnowledgeFragment:
     
    def is_empty(self):
        return len(self.predicates)==0
    
    predicates = None
    hashes = None
    
    # Return the key corresponding to the type of the item to be added/retrieved
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

    # builds the hash trees from an initial collection of predicates 
    def build_hash_trees(self, initial):
        for item in initial:
            insert(self.hashes[self.get_bin(item)], item.getindex(), item)
        self.predicates = self.predicates + initial# should never add duplicates...

    # inserts a predicate item (a fact) in the knowledge base
    def insert(self, item):
        self.build_hash_trees([item])

    # Tells if a fact is known or not.
    def __contains__(self, item):
        rtr = retrieve(self.hashes[self.get_bin(item)], item.getindex())
        if not rtr or not rtr[-1]:
            return False
        else:
            return rtr[-1].field == item.field

    def __str__(self):
        return str(map(str, self.predicates))

    # Initializes the knowledge base.
    def __init__(self, initial=None):
        if not initial:
            initial = []
        self.predicates = []
        self.hashes = {
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
        self.build_hash_trees(initial)
    # returns all the known Beg predicates.
    def begins(self):
        return filter(lambda x: isinstance(x, Beg), self.predicates)
    # returns all the known Len predicates.
    def lengths(self):
        return filter(lambda x: isinstance(x, Len), self.predicates)
    # returns all the known Val predicates.
    def values(self):
        return filter(lambda x: isinstance(x, Val), self.predicates)
    # returns all the known Pointer predicates.
    def pointers(self):
        return filter(lambda x: isinstance(x, Pointer), self.predicates)
    # returns all the known Rep predicates.
    def repeats(self):
        return filter(lambda x: isinstance(x, Rep), self.predicates)
    # returns all the known RepLen predicates.
    def repeatLengths(self):
        return filter(lambda x: isinstance(x, RepLen), self.predicates)

# Tell if predicate pred is known in knowledge base kbs 
def known(pred, kbs):
    for kb in kbs:
        if pred in kb:
            return True
    return False

# merge the knowledge of kb_new into kb_old; kb_old changes, kb_new does not.
def learn(kb_old, kb_new):
    kb_old.build_hash_trees(kb_new.predicates)

# Check if a premise applies (thus, a rule).
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


def add_inferences(rule, kb_old,
                   kb_last_round, kb_round):
    inferred = []
    
    for consequence in rule.consequences:

        known_in_earlier_rounds = known(consequence, [kb_old, kb_last_round])
        known_in_this_round = known(consequence, [kb_round])
        if not known_in_earlier_rounds:  # the consequence does not appear
            if not known_in_this_round:
                kb_round.insert(consequence)
                inferred.append(consequence)
        
    return inferred



def infer_generic(rule_constructor,
                  iteration,
                  responsible_premise,
                  other_premises,
                  kb_old,
                  kb_last_round,
                  kb_round,
                  consequences,
                  kbs,
                  applied_rules):
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
        rule = rule_constructor(all_premises, concrete_consequences)
        # here cost model should decide whether to apply now or later the rule
        # note: for jumps, i need to wait until all costs are evaluated.
        # Since I fire all forward and backward first, at this point 
        # I should know how much all the pointers I found should cost.
        appliable_rule = cost_model.cost(rule, applied_rules, kbs)
        if appliable_rule :
            inferred = add_inferences(appliable_rule,
                                      kb_old, kb_last_round,
                                      kb_round)
            if not inferred:
                return
            else :
                ## TODO for jumps the mechanism must be rethought
                # currently, the first appliable jump is executed.
                # What I have now is that this function computes the 
                # cost of the application of a rule and applies it immediately.
                # (So the cost does not actually make any difference.)
                 
                applied_rules.was_applied(rule, cost_model)
                print('I applied '+str(rule))
                print(map(str,inferred))
                return inferred
        
        # inferred_nodes = map(str, inferred)
        # premises_nodes = map(str, all_premises)
        # predicate_nodes = inferred_nodes + premises_nodes
        # rule_nodes = [(k, name) for k in premises_nodes] + \
        #              [(name, k) for k in inferred_nodes]
        # inference_graph.add_nodes_from(predicate_nodes, kind='predicate')
        # inference_graph.add_node(name, kind='rule', label=iteration)
        # inference_graph.add_edges_from(rule_nodes)
        #dot_printer.edge(all_premises, str(rule_constructor), inferred)
        

def next_field(field, derive):
    """
    return the field that is inc fields far
    :param field: 
    :param derive: function computing the new identifier from the given one 
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


def infer_forward(iteration, b, kb_old, kb_last_round, kb_round, kbs, applied_rules):
    # creation of second consequence, this is included in a function

    i_fw_field = next_field(b.field, add_some(1))
    if not i_fw_field:
        return
    return infer_generic(lambda pre, cons : ForwardBackward("forward",pre,cons),
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
                  kbs,
                  applied_rules
                  )


def infer_backward(iteration, b, kb_old, kb_last_round, kb_round, kbs, applied_rules):
    # creation of second consequence, this is included in a function
    i_bw_field = next_field(b.field, add_some(-1))
    if not i_bw_field:
        return
    return infer_generic(lambda pre, cons : ForwardBackward("backward",pre,cons),
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
                  kbs,
                  applied_rules
                  )


def infer_join(iteration, b, kb_old, kb_last_round, kb_round, kbs, applied_rules):
    i_jo_field = next_field(b.field, add_some(1))
    if not i_jo_field:
        return
    return infer_generic(Join,
                  iteration,
                  b,
                  [lambda x: Beg(i_jo_field)],
                  kb_old,
                  kb_last_round,
                  kb_round,
                  [
                      lambda x: Len(x.field),
                  ],
                  kbs,
                  applied_rules
                  )


def infer_jump_right(iteration, ptr, kb_old, kb_last_round, kb_round, kbs, applied_rules):
    return infer_generic(lambda pre, cons: Jump("right", pre, cons),
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
                  kbs,
                  applied_rules
                  )


def infer_jump_left(iteration, ptr, kb_old, kb_last_round, kb_round, kbs, applied_rules):
    return infer_generic(lambda pre, cons: Jump("left", pre, cons),
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
                  kbs,
                  applied_rules
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
    infer_generic(RepLen,
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
                      # Jumps should be executed separately, if none of 
                      # the above inferences resulted in new facts.
                      (infer_jump_left, pointers),
                      (infer_jump_right , pointers),
                      (infer_replen     , reps)]
    print("** In round **" + str(round_counter))
    # Below, the functor that runs the inference.
    # For a rule with n premises, it fires executes twice
    # with the responsibility *singleton* draw from, respectively,
    # the last round and the older.
    # The two invocations differ in where the rest of the premises might be found:
    # the second invocation accounts the configuration
    #  responsible in old kb, 
    def apply_inference(inf_fun, applied_rules):
        
        for responsible in inf_fun[1][0]: ## responsible in last round, 
            # so I am sure that whatever is inferred is new
            inf_fun[0](round_counter, responsible, kb_old, kb_last_round,
                       kb_round, [kb_old, kb_last_round], applied_rules)
        for responsible in inf_fun[1][1]: ## responsible in old rounds. 
            # Then at least one of the other premises must be draw from the last round.
            # Not all in kb_old, though!
            # FIXME Not sure if this becomes an error but I added kb_last_round
            inf_fun[0](round_counter, responsible, kb_old, kb_last_round,
                       kb_round, [kb_old, kb_last_round], applied_rules)
    applied_rules = ApplicationRound()
    for func in inference_funcs  :
        # func is a pair (inference_function, 
        #                   ([predicates inferred in last round]
        #                    [predicates inferred before last round])
        #                )
        apply_inference(func, applied_rules)
    
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

unknown = V()
second = P(unknown, 1)
beginning = P(second, 2)

layout = [beginning, second, unknown]
cost_model = CostModel(layout[0])

predicates = mu_labeling(layout)
predicates.append(Beg(beginning))
predicates_nodes = map(str, predicates)
inference_graph.add_nodes_from(predicates_nodes, kind='initial')
print(predicates_nodes)
initial_nodes = [u for (u, d) in inference_graph.nodes(data=True) if
                 d['kind'] == 'initial']
 
old = saturate(predicates)
# 
# pos = nx.spring_layout(inference_graph)  # positions for all nodes
# 
# rul_nodes = [(u, d) for (u, d) in inference_graph.nodes(data=True) if
#              d['kind'] == 'rule']
# label_dict = {}
# for (u, d) in rul_nodes:
#     label_dict[u] = d['label']
# rul_nodes = [list(l) for l in zip(*rul_nodes)][0]
# pred_nodes = [u for (u, d) in inference_graph.nodes(data=True) if
#               d['kind'] == 'predicate']
# 
# # nodes
# nx.draw_networkx_nodes(inference_graph, pos, node_size=70, nodelist=rul_nodes)
# nx.draw_networkx_nodes(inference_graph, pos, node_size=70, node_color='yellow',
#                        nodelist=pred_nodes)
# nx.draw_networkx_nodes(inference_graph, pos, node_size=70, node_color='blue',
#                        nodelist=initial_nodes)
# 
# # edges
# nx.draw_networkx_edges(inference_graph, pos,
#                        width=1)
# # labels
# nx.draw_networkx_labels(inference_graph, pos, labels=label_dict,
#                         font_color='yellow', font_size=10,
#                         font_family='sans-serif')
# nx.draw_networkx_labels(inference_graph, pos, font_size=10,
#                         font_color='blue', font_family='sans-serif')
# 
# plt.axis('off')
# #plt.savefig("weighted_graph.png") # save as png
# plt.show() # display
dot_printer.write("prova")