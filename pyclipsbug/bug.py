import clips

clips.Load("clips.clp")
clips.Reset()

tmp = clips.FindTemplate("tempeh")
print tmp.PPForm()
f1 = clips.Fact(tmp)
f1_slotkeys = f1.Slots.keys()
print f1_slotkeys
print "please print this"
print f1.PPForm()
print "print this other"
