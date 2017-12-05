
; -*- mode: Clojure; -*-
; This is *not* Clojure code, it's Chicken Scheme, but it looks better this way
; on github.

; Another directed graph module? I know, I know.
; The problem is, the "digraph" egg doesn't support removal of individual
; edges, and the "graphs" module has a bug when you remove edges.  Apparently
; removing edges is risky biscuits.
; This minimal digraph implementation does only a little more than I need it to
; for an "uninstall" routine I'm writing.  Enjoy.

; A digraf is a directed graph.  I chose the name 'digraf' because the module
; name 'digraph' was already taken.
;
; A digraf contains vertices, which are any objects that can be compared using
; srfi-128's default comparator's equality predicate.  So, most things.
;
; Vertices are joined by directed edges.  An _edge_ is an arrow with its tail
; at one vertex (documented as "from") and its head at another, or possibly the
; same, vertex (documented as "to").  If a vertex is either of an edge's tail
; or head, then that edge is considered _coincident_ with the vertex.
;
; Edges coincident with a vertex such that the vertex is the _tail_ of the edge
; are called _outward_ edges of the vertex.  The heads of those same edges are
; called outward neighbors of the vertex (or, alternatively, successors).
; 
; Edges coincident with a vertex such that the vertex is the _head_ of the edge
; are called _inward_ edges of the vertex. The tails of those same edges are
; called inward neighbors of the vertex (or, alternatively, predecessors).
;
; A vertex's _indegree_ is its number of inward edges.  A vertex's _outdegree_
; is its number of outward edges, and a vertex's _degree_ is its number of
; total coincident edges.
;
; digraf uses srfi-113 sets to store edges, and it uses srfi-69 hash tables to
; map vertices to their groups of inward and outward neighbors, the groups
; themselves being srfi-113 sets.  Here's what's inside:
;
;     digraf:
;
;         edges: (set ... (from1 . to1) (from2 . to2) ...)
;
;         vertices = hash-table:
; 
;             vertex -> ($ vertex-edges (set ... inward-vertex ...)
;                                       (set ... outward-vertex ...))
;
; That is, a digraph contains a set of edges (where an edge is a pair of
; vertices) and a hash table used to associate a vertex with its set of
; inward vertices and its set of outward vertices.
;
; digraf objects are mutable and ready to party.  Mutating methods return their
; (mutated in place) digraf argument.

(module set-utils
  ; convenient extensions to srfi-113 
  (set*
   list->set*
   default-comparator
   are-equal?)

  (import chicken scheme)
  (use miscmacros  ; miscellaneous macros (define-syntax-rule)
       srfi-113    ; sets
       srfi-128)   ; comparators

  (define default-comparator (make-default-comparator))
  
  (define are-equal? (comparator-equality-predicate default-comparator))

  ; macro wrappers around the 'set' constructors, using a default comparator
  (define-syntax-rule (set* args ...)
    (set default-comparator args ...))

  (define-syntax-rule (list->set* lst)
    (list->set default-comparator lst)))

(module digraf
  ; directed graph
  (digraf
   digraf?
   digraf-edge?
   digraf-vertex?
   digraf-edges
   digraf-edges-list
   digraf-vertices
   digraf-vertices-list
   digraf-outward
   digraf-outward-list
   digraf-inward
   digraf-inward-list
   digraf-indegree
   digraf-outdegree
   digraf-degree
   digraf-copy
   digraf-remove-edge!
   digraf-remove-edges!
   digraf-remove-vertex!
   digraf-remove-vertices!
   digraf-add-edge!
   digraf-add-edges!
   digraf-add-vertex!
   digraf-add-vertices!)

  (import chicken 
          scheme
          set-utils)

  (use srfi-1            ; lists
       srfi-69           ; hash tables
       srfi-113          ; sets
       srfi-128          ; comparators
       srfi-133          ; vectors (vector-fold)
       clojurian-syntax  ; -> and other macros
       data-structures   ; conc
       defstruct         ; simplified record definitions
       matchable         ; pattern matching
       ports)            ; input/output (with-output-to-port)

  ; types
  (defstruct vertex-edges
             inward    ; set[vertex]
             outward)  ; set[vertex]

  ; The fields of 'digraf' end in asterisks so that the accessor functions
  ; don't collide with those exported by this module (e.g. digraf-vertices).
  (defstruct digraf
             vertices*  ; hash-map[vertex -> vertex-edges]
             edges*)    ; set[(vertex . vertex)]

  (define-record-printer (digraf graf port)
    ; Print a digraf like this:
    ;
    ; digraf:
    ;     A -> &set[ B C ]
    ;     B -> &set[ C ]
    ;     C -> &set[ ]
    (with-output-to-port port (lambda ()
      (print "digraf:")
      (hash-table-for-each
        (digraf-vertices* graf)
        (match-lambda* [(vertex ($ vertex-edges inward outward))
          (print "    " vertex " -> " outward)])))))

  ; procedures
  (define (fold* proc init seq . others)
    ; generic fold
    (cond [(list? seq) (apply fold `(,proc ,init ,seq ,@others))]
          [(vector? seq) (apply vector-fold `(,proc ,init ,seq ,@others))]
          
          [(not (null? others))
           (error (conc "fold* called on neither a vector nor a list, and yet "
                        "trailing arguments were specified.  fold* supports "
                        "multiple sequences only for vectors and lists.  Here "
                        "are the trailing arguments: "
                        others))]
          
          [(set? seq) (set-fold proc init seq)]
          [(hash-table? seq) (hash-table-fold seq proc init)]
          [else (error (conc "fold* not defined for type of " seq))]))

  (define (update-vertices! vertices vertex which neighbor)
    ; Update the hash-table 'vertices' by adding 'neighbor' to either the
    ; inward or outward edges set associated with 'vertex', where 'which'
    ; determines whether to select the inward set or the outward set.
    (hash-table-update!/default
      vertices  ; hash-table to update
      vertex    ; key at which to update
      (lambda (edges)  ; updater function (old value -> new value)
        (set-adjoin! (which edges) neighbor)
        edges)
      (make-vertex-edges inward: (set*) outward: (set*))))  ; default value

  (define (add-edge-to-vertices! vertices edge)
    (match edge [(from . to)
      (update-vertices! vertices from vertex-edges-outward to)
      (update-vertices! vertices to vertex-edges-inward from)
      vertices]))

  (define (make-vertices edges)
    ; Return a hash-table that maps vertices to (inward . outward) edge set
    ; pairs, calculated from the list of pairs (from . to) 'edges'.
    ; For example:
    ;
    ;     (make-vertices '((A . B) (A . C) (B . C)))
    ;
    ; is a hash-table with the following structure:
    ;
    ;     'A -> (make-vertex-edges inward: (set*)       outward: (set* 'B 'C))
    ;     'B -> (make-vertex-edges inward: (set* 'A)    outward: (set* 'C))
    ;     'C -> (make-vertex-edges inward: (set* 'A 'B) outward: (set*))
    ;
    ; 'edges' may be a list, vector, or set.
    ;
    (fold* (lambda (edge vertices) (add-edge-to-vertices! vertices edge))
           (make-hash-table)
           edges))

  (define (digraf #!optional (edges '()))
    ; Create a directed graph containing the optionally specified 'edges'.
    ; Create vertices as necessary based on their mention in 'edges'.  If
    ; specified, 'edges' is a list of pairs (from . to), where 'from' and 'to'
    ; are vertices.
    (make-digraf vertices*: (make-vertices edges)
                 edges*:    (list->set* edges)))

  (define match-edge (match-lambda
    ; Return a pair (from . to) extracted from the specified list.
    [((from . to)) (cons from to)]
    [(from to)     (cons from to)]
    [other         (error (conc "An edge must be specified as either a pair "
                                "(from . to) or as two arguments: from, to. "
                                "Instead the following were given: " other))]))

  (define (digraf-edge? graf . args)
    ; Return whether the specified edge is in 'graf'.  The edge may be
    ; specified either as a pair (from . to) or vertices, or as two vertex
    ; arguments: from, to.
    (set-contains? (digraf-edges* graf) (match-edge args)))

  (define (digraf-vertex? graf vertex)
    ; Return whether 'vertex' is in 'graf'.
    (hash-table-exists? (digraf-vertices* graf) vertex))

  (define (digraf-edges-list graf)
    ; Return the edges of 'graf' as an association list ((from . to) ...),
    ; where 'from' and 'to' are vertices.
    (-> graf digraf-edges* set->list))

  (define (digraf-edges graf)
    ; Return the edges of 'graf' as a set of (from . to) pairs, where 'from'
    ; and 'to' are vertices.
    (-> graf digraf-edges* set-copy))
  
  (define (digraf-vertices-list graf)
    ; Return the vertices of 'graf' as a list.
    (-> graf digraf-vertices* hash-table-keys))

  (define (digraf-vertices graf)
    ; Return the vertices of 'graf' as a set.
    (-> graf digraf-vertices-list list->set*))

  (define (inward/outward-ref graf vertex which-way)
    ; Return the set of either inward or outward neighbors of 'vertex' in
    ; 'graf', where 'which-way' is one of the getter methods of vertex-edges
    ; (and is used get either the inward or outward neighbors).
    (-> graf digraf-vertices* (hash-table-ref vertex) which-way))

  (define (outward-ref graf vertex)
    ; Return the set of outward neighbors of 'vertex' in 'graf'.
    (inward/outward-ref graf vertex vertex-edges-outward))

  (define (digraf-outward graf vertex)
    ; Return a copy of the set of outward neighbors of 'vertex' in 'graf'.
    (set-copy (outward-ref graf vertex)))

  (define (digraf-outward-list graf vertex)
    ; Return a list of the outward neighbors of 'vertex' in 'graf'.
    (set->list (outward-ref graf vertex)))

  (define (inward-ref graf vertex)
    ; Return the inward neighbors of 'vertex' in 'graf'.
    (inward/outward-ref graf vertex vertex-edges-inward))

  (define (digraf-inward graf vertex)
    ; Return a copy of the inward neighbors of 'vertex' in 'graf'.
    (set-copy (inward-ref graf vertex)))

  (define (digraf-inward-list graf vertex)
    ; Return a list of the inward neighbors of 'vertex' in 'graf'.
    (set->list (inward-ref graf vertex)))

  (define (digraf-indegree graf vertex)
    ; Return the number of inward edges coincident with 'vertex' in 'graf'.
    (set-size (inward-ref graf vertex)))

  (define (digraf-outdegree graf vertex)
    ; Return the number of outward edges coincident with 'vertex' in 'graf'.
    (set-size (outward-ref graf vertex)))

  (define (digraf-degree graf vertex)
    ; Return the number of edges coincident with 'vertex' in 'graf'.
   
    ; The more elegant
    ;
    ;     (+ (digraf-indegree  graf vertex)
    ;        (digraf-outdegree graf vertex))
    ;
    ; would incur a redundant hash-table lookup, so do this instead:
    (match (hash-table-ref (digraf-vertices* graf) vertex)
      [($ digraf inward outward)
       (+ (set-size inward) (set-size outward))]))

  (define (digraf-copy graf)
    ; Return a shallow copy of 'graf'.  The structure of the returned value
    ; will be distinct from 'graf', but the vertices of the copy will refer to
    ; the same objects as in 'graf'.
    (match graf
      [($ digraf vertices edges)
       (make-digraf
         vertices*:
           (fold*
             (match-lambda* [(vertex ($ vertex-edges inward outward) the-copy)
               (hash-table-set!
                 the-copy
                 vertex
                 (make-vertex-edges inward: (set-copy inward)
                                    outward: (set-copy outward)))
               ; (print "vertices so far: " (hash-table->alist the-copy))
               the-copy])
             (make-hash-table)
             vertices)
         edges*:
           (set-copy edges))]))

  (define (remove-coincident! graf edge)
    ; Remove data from the appropriate vertex-edges in 'graf' to be consistent
    ; with the removal of 'edge' from 'graf'.
    (match-let* ([(from . to) edge]
                 [vertices (digraf-vertices* graf)])
      
      ; Remove 'to' from the outward vertex-edges of 'from', if it's there.
      (match (hash-table-ref/default vertices from #f)
        [($ vertex-edges inward outward) (set-delete! outward to)]
        [#f #f])

      ; Remove 'from' from the inward vertex-edges of 'to', if it's there.
      (match (hash-table-ref/default vertices to #f)
        [($ vertex-edges inward outward) (set-delete! inward from)]
        [#f #f])

      ; Return 'graf'.
      graf))

  (define (digraf-remove-edge! graf . args)
    ; Remove the specified edge from 'graf' and return 'graf'.  The edge can
    ; be specified as a pair (from . to) or as two arguments: from, to.
    (let ([edge  (match-edge args)]
          [edges (digraf-edges* graf)])
     
      ; Remove the 'edge' from 'edges'.
      (set-delete! edges edge)

      ; Remove references to the edge in vertex-edges, and return the modified
      ; digraf.
      (remove-coincident! graf edge)))
          
  (define (digraf-remove-edges! graf edges)
    ; Remove each of the 'edges' from 'graf' and return 'graf'.  'edges' must
    ; be a sequence of (from . to) pairs.
    (fold* (lambda (edge graf)  (digraf-remove-edge! graf edge))
           graf
           edges))

  (define (digraf-remove-vertex! graf vertex)
    ; Remove 'vertex' and all of its edges from 'graf'.
    (match graf [($ digraf vertices edges)

      ; Remove coincident edges (from the edge set and from vertex-edges).
      (set-filter! (lambda (edge)
                     (match-let*
                       ([(from . to) edge]
                        [keep (and (not (are-equal? vertex from))
                                        (not (are-equal? vertex to)))])
                         ; If this edge is going to be removed, then also
                         ; remove references to it in vertex-edges objects.
                         (unless keep
                           (remove-coincident! graf edge))

                         keep))
                   edges)

      ; Remove the vertex.
      (hash-table-delete! vertices vertex)

      ; Return graf.
      graf]))

  (define (digraf-remove-vertices! graf vertices)
    ; Remove the 'vertices' and their edges from 'graf' and return 'graf'.
    (fold* (lambda (vertex graf) (digraf-remove-vertex! graf vertex))
           graf
           vertices))

  (define (digraf-add-edge! graf . args)
    ; Add the specified edge to 'graf' and return 'graf'.  The edge can be
    ; specified as a pair (from . to) or as two arguments: from, to.
    (let ([edge        (match-edge args)]
          [edges       (digraf-edges* graf)]
          [vertices    (digraf-vertices* graf)])
      (set-adjoin! edges edge)
      (add-edge-to-vertices! vertices edge)
      graf))

  (define (digraf-add-edges! graf edges)
    ; Add the 'edges' to 'graf' and return 'graf'.  'edges' must be a sequence
    ; of (from . to) pairs.
    (fold* (lambda (edge graf) (digraf-add-edge! graf edge))
           graf
           edges))

  (define (digraf-add-vertex! graf vertex)
    ; Add the 'vertex' to 'graf' and return 'graf'.
    (-> graf 
        digraf-vertices* 
        (hash-table-set! vertex (make-vertex-edges inward: (set*)
                                                   outward: (set*))))
    graf)

  (define (digraf-add-vertices! graf vertices)
    ; Add the 'vertices' sequence to 'graf' and return 'graf'.
    (fold* (lambda (vertex graf) (digraf-add-vertex! graf vertex))
           graf
           vertices)))

; MIT License
; 
; Copyright (c) 2017 David Goffredo
; 
; Permission is hereby granted, free of charge, to any person obtaining a copy
; of this software and associated documentation files (the "Software"), to deal
; in the Software without restriction, including without limitation the rights
; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
; copies of the Software, and to permit persons to whom the Software is
; furnished to do so, subject to the following conditions:
; 
; The above copyright notice and this permission notice shall be included in
; all copies or substantial portions of the Software.
; 
; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
; SOFTWARE.
