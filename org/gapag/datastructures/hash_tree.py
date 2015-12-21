# key is a list of strings/ints

class HashTree:
    def __init__(self, branches=None, val=None):
        if branches is None:
            self.branches = {}
        else:
            self.branches = branches
        if val is None:
            self.val = {}
        else:
            self.val = val


class LeaveIt:
    def __init__(self):
        pass


class ArgumentError(Exception):
    pass


def size(tree):
    return reduce(
        lambda x, y: x + y,
        map(size, [tree.branches[x] for x in tree.branches]),
        len([x for x in tree.val if tree.val[x]])
    )


def get_all_below(tree):
    return reduce(
        lambda x, y: x + y,
        map(get_all_below, [tree.branches[x] for x in tree.branches]),
        [tree.val[x] for x in tree.val if tree.val[x]]
    )


def between(tree, key1, key2):
    comp = key1 > key2
    if key1 == key2:
        return []
    elif comp:
        tmp = key2
        key2 = key1
        key1 = tmp
    # count all the fields
    indexes = zip_longest(0, key1, key2)
    trees = zip_longest(None, retrieve_trees(tree, key1)[1],
                        retrieve_trees(tree, key2)[1])
    return all_values_between(indexes, trees)


def zip_longest(pad_element, *lists):
    max_len = max(map(len, lists))
    return zip(*map(lambda x: x + ([pad_element] * (max_len - len(x))), lists))


def insert(tree, key, value):
    """
    Inserts the list of values in the appropriate keys
    :param tree: 
    :param key: 
    :param value: 
    :return: 
    """
    # check that lists have same length    
    if isinstance(value, list):
        insert_list(tree, key, value)
    else:
        list_value = ([None] * (len(key) - 1))
        list_value.append(value)
        insert_list(tree, key, list_value)


def insert_list(tree, key, value):
    diff = len(key) - len(value)
    if diff < 0:
        raise ArgumentError
    else:
        value = ([LeaveIt()] * diff) + value
    try:

        for (k, v) in zip(key, value):
            # put the leftmost value in val[k] (overwriting)
            if diff == 0:
                tree.val[k] = v
            else:
                if k not in tree.val:
                    tree.val[k] = None
                diff -= 1
            if k not in tree.branches:
                tree.branches[k] = HashTree()
            tree = tree.branches[k]
    except KeyError:
        return None


def all_values_between(indexes, trees):
    all_values = []
    for ((ind_begin, ind_end), (tree_begin, tree_end)) in zip(indexes, trees):
        if tree_begin == tree_end:  ### are they the same?
            rng = range(ind_begin,
                        ind_end + 1)  ## if they're the same this should always be positive
            tree_range = rng[1:-1]
            all_values = all_values + visit_content(tree_begin, rng, tree_range)
        else:  ## Not the same
            ## Handle left tree

            if not tree_begin:
                last_begin = 0
            else:
                last_begin = len(tree_begin.val)

            rng = range(ind_begin, last_begin)
            tree_range = rng[1:]
            all_values = all_values + visit_content(tree_begin, rng, tree_range)
            ## Handle right tree
            rng = range(0, ind_end + 1)
            tree_range = rng[:ind_end]
            all_values = all_values + visit_content(tree_end, rng, tree_range)
    return all_values


def visit_content(tree, rng, tree_range):
    # this node's values, that are not None:
    content = [tree.val[i] for i in rng
               if get_or_none(lambda: tree.val[i])]
    trees_below = [tree.branches[i] for i in tree_range
                   if get_or_none(lambda: tree.branches[
            i])]  # list of trees to explore all the way down
    return reduce(lambda x, y: x + y, map(get_all_below, trees_below), content)


def retrieve_trees(tree, key):
    """
    Return a list of pairs (value, tree containing the value), one element
     for each key segment.
    :param tree: 
    :param key: 
    :return: the list. If the key exceeds the depth of the tree, 
    the list is completed with values (None, None)
    """
    value = []
    trees = []
    for k in key:
        value.append(get_or_none(lambda: tree.val[k]))
        trees.append(tree)
        tree = get_or_none(lambda: tree.branches[k])
    return value, trees


def get_or_none(fun):
    try:
        return fun()
    except:
        return None


def retrieve(tree, key):
    rs = retrieve_trees(tree, key)
    if rs:
        rs = rs[0]
    else:
        rs = None
    return rs


def remove(tree, key):
    """
    **Unimplemented**
    :param tree: 
    :param key: 
    :return: 
    """
    pass

# my_hash = HashTree()
# insert(my_hash,[1,2,3],'pippone')
# insert(my_hash,[1,2,2],'pippe')
# insert(my_hash,[1,3],'teddy')
# print(retrieve(my_hash, [1,2,3]))
# print get_all_below(my_hash)
