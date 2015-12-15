# key is a list of strings/ints

class HashTree:
    def __init__(self, branches={}, val={}):
        self.branches = branches
        self.val = val

class LeaveIt:
    def __init__(self):
        pass


class ArgumentError(Exception):
    pass

def insert(tree, key, value):
    """
    Inserts the list of values in the appropriate keys
    :param tree: 
    :param key: 
    :param value: 
    :return: 
    """
    # check that lists have same length    
    if isinstance(value,list) :
        insert_list(tree, key, value)
    else:
        try:
            for k in key:
                if(k not in tree.branches):
                    tree.branches[k] = HashTree()
                if(k not in tree.val):
                    tree.val[k] = None
                tree = tree.branches[k]
            tree.val[k] = value
        except KeyError:
            return None

def insert_list(tree, key, value):
    diff = len(key)-len(value)
    if diff < 0:
        raise ArgumentError
    else:
        value = ([LeaveIt()]*diff)+value
    try:
        for (k,v) in zip(key,value):
            # put the leftmost value in val[k] (overwriting)
            if diff==0:
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

def retrieve(tree, key):
    value = []
    try:
        for k in key:
            value.append(tree.val[k])
            tree = tree.branches[k]
    except KeyError:
        return None    
    return value

def remove(tree, key):
    """
    **Unimplemented**
    :param tree: 
    :param key: 
    :return: 
    """
    pass

