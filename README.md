Horn Binary (De)Serialization Analysis
======================================
This software is a Python implementation of the paper *Horn Binary Serialization
 Analysis* accepted at the [HCVS2016 workshop](http://hcvs2016.it.uu.se/)

# Requirements
  * [Python 2.7](https://www.python.org/download/releases/2.7/) 
    * pyparsing (to install: `python -m pip install pyparsing`)
  * [CLIPS expert system] (http://clipsrules.sourceforge.net/), which must be 
    available on your path so that Python can call it. 
    
# Usage
Running `python main.py -h` shows the available arguments. 

## Layout mini-language
A layout is a sequence of fields. There are four possible fields.

 * `f` : Fixed length field
      
 * `v` : Varfield (that is, variable length fields)
      
 * `(X -> N)` : Pointers
      
 * `[F]*` : Repetition
      

where:

 * `X` is a label: any alphabetic word included between angular parentheses, e.g.
 `<anIdentifier>`
 * `N` is a number, i.e. a sequence of numeric digits.
 * `F` is a sequence of any of the above fields.

Any field can be followed by an identifier in `X`; and that identifier, that 
 must be unique, can be used to refer to the annotated field in almost any 
 pointer field: generally a pointer field cannot point inside a repetition.
 Check the paper for more information.

Examples:

```(<her> -> 1) v<her>```

```(<him> -> 7) f f<him> (<her> -> 2) v f<her> v f f f```

```(<me> -> 6)<me> v f<her> v f (<her> -> 3)```

# Implementation
`main.py` processes the layout definition transforming it to a form that is 
essentially the one described in the paper. 
 
This form is then translated to a set of predicates representing the initial 
knowledge, following the shape and methods described in the paper. 

The CLIPS rules embedded in the variable `engine` in `main.py` mostly encode 
the axioms described in the paper, plus some other machinery to actually be 
able to detect what happened in the knowledge base. Refer to the source code, 
the contents  of the `engine` variable in `main.py`, and to the CLIPS language 
reference for more information.
  
The CLIPS interpreter, opened as a subprocess, receives the facts extracted 
from the input layout together with the CLIPS rules as input.  

The Python script analyzes the output of the interpreter and tells if the 
layout is deserializable or not.

# Further notes
I wished to use the [pyclips library](https://github.com/almostearthling/pyclips
) to spare you installing manually the CLIPS interpreter but I could not get it 
working the way I wanted.

The language this software accepts is a simplified version of the one presented
on the paper; not in expressivity but in its shape.

For being able to refer to each field univocally the paper sets up a labelling
framework by means of lists of integers. This is handy in the paper, but 
you would generally like better to be able to refer with a mnemonic to the parts
of the layout that matter for you.

A big difference with the paper is, instead, that this implementation allows
pointers to point to more outer scopes. There are two reasonable extensions 
to what described in the paper, highlighted in the following two instances:

1. ```f f [(<hej>->1)]*<hej> f```

2. ```f f [(<uhh>->2)<uhh>]* f<hee>```

The above two would not be legal in the paper description.
The above can be included in a more general framework by pointing out that what
 eventually matters with pointers is that

* what it is being pointed is not ambiguous 

* how one counts the span from the offset.

In 1. the repetition `<hej>` contains a variable number of fields that tell the 
repetitions' length. This layout is deserializable because as soon as the parser
reads the first occurrence of the pointer, it knows where the whole repetition
will end.

In 2. the semantics of the span is: keep counting, overflowing to the next 
field. That is, `<uhh>->2)<uhh>` counts itself, all the fields in following it 
until the end of the repetition, plus `f<hee>`

I implemented 1. because it seems more reasonable (the stream might periodically
tell you what much is left to consume) and, to my subjective judgement more 
intuitive. 2. is in principle easy to implement but one needs to slightly change
 the axioms and most notably to introduce in the axioms some awareness about
 the shape of the layout under analysis; or, in other words, the jump axioms
 likewise facts should be generated in a per-layout fashion. I will implement it...
 later.