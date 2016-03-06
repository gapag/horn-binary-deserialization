import horn
import os
class FromFile:
    def __init__(self):
        pass
    def testFromFile(self):
        # load definition file
        with open('examples','r') as f, open('results','w') as rsl:
            for spec in f:
                if spec and len(spec)>1:
                    if spec[0] != '#':
                        r = horn.analyseSpec(spec, 'testoutput.clp')
                        rsl.write("%s : %d\n"%(spec, r))

a = FromFile()
a.testFromFile()