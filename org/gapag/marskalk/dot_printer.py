
class DotPrinter :

    dottext = []

    def __init__(self):
        self.dottext = []


    def rule_node(self, name):
        return "{} [shape = box]".format(name)

    def edge(self, premises, rule, consequences):

        frm = "{{{!s}}} -> {{{!s}}}"
        r = dot_friendly(rule)
        prem = ";".join(map(str, premises))
        cons = ";".join(map(str, consequences))
        self.dottext.append(frm.format(prem,r))
        self.dottext.append("{} [shape=box]".format(r))
        self.dottext.append(frm.format(r, cons))

    def write(self, name):
        f = open(name, 'w')
        f.write("digraph G{\n")
        f.write('size = "10,10";\n')
        f.write("\n".join(self.dottext))
        f.write('\n}')
        f.close()

def dot_friendly(s):
    return s.replace(",","_").replace("[","_").replace("]","_").replace("(","_").replace(")","_").replace(" ","_")