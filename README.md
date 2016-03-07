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
Running `main.py -h` shows the available arguments. 

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
The layout mini-language is processed to a form that is essentially the one 
 described in the paper. This form is then translated to a set of predicates,
 these too following the shape described in the paper, which represent the 
 initial knowledge of a parser. This facts together with the CLIPS rules 
 embedded in the variable `engine` are sent to the CLIPS interpreter, opened
  as a subprocess. The Python script analyzes the output and tells if the 
  layout is deserializable or not.

# Further notes
I wished to use the [pyclips library](https://github.com/almostearthling/pyclips
) to spare you installing manually the CLIPS interpreter but I could not get it 
working the way I wanted.

The language this software accepts is a simplified version of the one presented
on the paper; not in expressivity but in its shape.

For being able to refer to each field univocally the paper sets up a labelling
framework by means of lists of integers. This is handy in the paper but not in
real world. 