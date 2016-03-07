import horn
import os
class FromFile:
    def __init__(self):
        pass
    def testFromFile(self):
        # load definition file
        with open('examples.txt','r') as f, open('results','w') as rsl:
            for spec in f:
                if spec and len(spec.strip())>0:
                    if spec[0] != '#':
                        print "testing %s" %spec
                        r = horn.analyseSpec(spec, 'testoutput.clp')
                        rsl.write("%s : %d\n"%(spec, r))

a = FromFile()
a.testFromFile()