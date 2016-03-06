(deftemplate beg
  "Beginning of an item"
  (multislot index
	(type INTEGER)
	(default  0 )
	)
)

(deftemplate len
  "Length of an item"
  (multislot index
	(type INTEGER)
	(default  0 )
	)
)

(deftemplate replen
  "Length of repetition"
  (multislot index
	(type INTEGER)
	(default  0 )
	)
)

(deftemplate val
  "value of an item"
  (multislot index
	(type INTEGER)
	(default  0 )
	)
)

(deftemplate ptr
  "Pointer"
  (multislot index
	     (type INTEGER)
	     (default 0))
  (multislot offset
	     (type INTEGER)
	     (default 0))
  (slot span
	     (type INTEGER)
	     (default 0))
)

(deftemplate repeat
  "Repeat item"
  (multislot index
	     (type INTEGER)
	     (default 0))
    (slot span
	     (type INTEGER)
	     (default 0))
)
		   

(defrule read-and-forward
  (beg (index ?id $?rest))
  (len (index ?id $?rest))
  =>
  (assert (val (index ?id ?rest)))
  (assert (beg (index (+ ?id 1) ?rest)))
)

(defrule join
  (beg (index ?id $?rest))
  (beg (index ?oid&:(= ?oid (+ ?id 1)) $?rest))
  =>
  (assert (len (index ?id ?rest)))
)

(defrule backward  
  (len (index ?id $?rest))
  (beg (index ?oid&:(= ?oid (+ ?id 1)) $?rest))
  =>
  (assert (beg (index ?id ?rest)))
)


(defrule count-right
  (ptr (offset ?ptrhead $?tail) (span ?l) (index $?label))
  (val (index $?label))
  (beg (index ?ptrhead $?tail))
  =>
  (assert (beg (index (+ ?ptrhead ?l) ?tail)))
)

(defrule count-left
  (ptr (offset ?ptrhead $?tail) (span ?l) (index  $?label))
  (val (index $?label))
  (beg (index ?q&:(= ?q (+ ?ptrhead ?l)) $?tail))

  =>
  (assert (beg (index ?ptrhead $?tail)))
)

(defrule enter-repeat
  (repeat (index ?a $?rest )(span ?len) )
  (beg (index ?a $?rest))
  (beg (index ?q&:(= ?q (+ ?a 1)) $?rest))
  ;(val (index $?ptrlocation)) ; I think these two predicates are unnecessary, I thought about them when I did not understand the preprocessing step
  ;(ptr (offset ?before-repeat&:(<= ?before-repeat ?a) $?rest )
  ;     (span ?ptrlen&:(> ?ptrlen (- ?a ?before-repeat))) ; I think should be > instead of >=
  ;     (index $?ptrlocation))
  =>
  (assert (beg  (index 0 ?a ?rest)))
  (assert (beg (index ?len ?a ?rest)))
  (assert (replen (index ?a $?rest)))
)


(deffacts initial-knowledge "Test"
  (beg (index 0))
  (len (index 0))
)

(deftemplate unknownLength
  "unknown length item"
  (multislot index
	(type INTEGER)
	(default  0 )
	)
)

(defrule check-all-variable-lengths-are-found
  (unknownLength (index $?s))
  (not (len (index $?s)))
  =>
  (assert (variable-not-found))
)

(defrule check-all-repeats-have-length
  (unknownLength (index $?s))
  (repeat (index $?s) )
  (not (replen (index $?s)))
  =>
  (assert (repeat-not-bounded))
)

(deffunction test-all-unknown-lengths-were-found ()
  (if
      (any-factp ((?vv variable-not-found)) (eq 1 1));?first:index
      then
    FALSE
    else
    TRUE
    )
  )

(deffunction test-all-repeats-were-bounded ()
      (if
	(any-factp ((?rep repeat-not-bounded)) (= 1 1));?first:index))
	then
	FALSE

        else
	  TRUE
	  )
)

