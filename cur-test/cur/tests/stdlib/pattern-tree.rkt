#lang cur
(require cur/stdlib/pattern-tree
         cur/stdlib/bool
         cur/stdlib/nat
         (except-in cur/stdlib/list
                    cons)
         (for-syntax rackunit))

;; NESTED TREE TESTS

(begin-for-syntax
  ; simple
  (check-true
   (pt-equal? (create-pattern-tree
                   #'((n m)
                      ([z z => A]
                       [z (s x) => B]))
                   #:env (list
                          (cons #'n #'Nat)
                          (cons #'m #'Nat)))
                  (pt-decl
                   #'n
                   (list
                    (pt-match
                     #'z
                     (pt-decl
                      #'m
                      (list
                       (pt-match
                        #'z
                        (pt-body #'A))
                       (pt-match
                        #'(s x1)
                        (pt-body #'B)))))))))

  ; body identifiers rebound
  (check-true
   (pt-equal? (create-pattern-tree
                   #'((n)
                      ([n => n]))
                   #:env (list
                          (cons #'n #'Nat)))
                  (pt-decl
                   #'n
                   (list
                    (pt-match
                     #'n
                     (pt-body #'n))))))

  ; body identifiers rebound for arguments
  (check-true
   (pt-equal? (create-pattern-tree
                   #'((n m)
                      ([(s y) z => y]
                       [(s w) (s x) => x]))
                   #:env (list
                          (cons #'n #'Nat)
                          (cons #'m #'Nat)))
                  (pt-decl
                   #'n
                   (list
                    (pt-match
                     #'(s y2)
                     (pt-decl
                      #'m
                      (list
                       (pt-match
                        #'z
                        (pt-body #'y2))
                       (pt-match
                        #'(s x3)
                        (pt-body #'x3)))))))))

  ; body identifiers rebound for arguments; in the case of shadowing
  ; we choose to simplify it by naively performing substitution without
  ; checking subsequent patterns for the pattern variable
  ; potential TODO item?
  (check-true
   (pt-equal? (create-pattern-tree
                   #'((n m)
                      ([(s y) z => y]
                       [(s x) (s x) => x]))
                   #:env (list
                          (cons #'n #'Nat)
                          (cons #'m #'Nat)))
                  (pt-decl
                   #'n
                   (list
                    (pt-match
                     #'(s y4)
                     (pt-decl
                      #'m
                      (list
                       (pt-match
                        #'z
                        (pt-body #'y4))
                       (pt-match
                        #'(s x5)
                        (pt-body #'y4)))))))))


  ; pattern variable single
  (check-true
   (pt-equal? (create-pattern-tree
                   #'((n m)
                      ([a z => a]))
                   #:env (list
                          (cons #'n #'Nat)
                          (cons #'m #'Nat)))
                  (pt-decl
                   #'n
                   (list
                    (pt-match
                     #'a
                     (pt-decl
                      #'m
                      (list
                       (pt-match
                        #'z
                        (pt-body #'n)))))))))

  ; merge pattern variable trivial
  (check-true
   (pt-equal? (create-pattern-tree
                   #'((n m)
                      ([a z => a]
                       [z (s x) => x]
                       [(s x) (s y) => C]))
                   #:env (list
                          (cons #'n #'Nat)
                          (cons #'m #'Nat)))
                  (pt-decl
                   #'n
                   (list
                    (pt-match
                     #'z
                     (pt-decl
                      #'m
                      (list
                       (pt-match
                        #'(s x6)
                        (pt-body #'x6))
                       (pt-match
                        #'z
                        (pt-body #'n)))))
                    (pt-match
                     #'(s x7)
                     (pt-decl
                      #'m
                      (list
                       (pt-match
                        #'(s y8)
                        (pt-body #'C))
                       (pt-match
                        #'z
                        (pt-body #'n)))))
                    (pt-match ; note: always keep the pattern variable case!
                     #'a
                     (pt-decl
                      #'m
                      (list
                       (pt-match
                        #'z
                        (pt-body #'n)))))))))

  ; merge pattern variable overwrite by order
  (check-true
   (pt-equal? (create-pattern-tree
               #'((n m)
                  ([(s x) z => A]
                   [a z => a]
                   [z z => C]))
               #:env (list
                      (cons #'n #'Nat)
                      (cons #'m #'Nat)))
              (pt-decl
               #'n
               (list
                (pt-match
                 #'(s x9)
                 (pt-decl
                  #'m
                  (list
                   (pt-match
                    #'z
                    (pt-body #'A)))))
                (pt-match
                 #'z
                 (pt-decl
                  #'m
                  (list
                   (pt-match
                    #'z
                    (pt-body #'C))))) ; this body was provided first
                (pt-match
                 #'a
                 (pt-decl
                  #'m
                  (list
                   (pt-match
                    #'z
                    (pt-body #'n)))))))))

  ; slightly more complicated / realistic example
  (check-true
   (pt-equal? (create-pattern-tree
               #'((n m)
                  ([z _ => z]
                   [(s n-1) z => (s n-1)]
                   [(s n-1) (s m-1) => (bad-minus n-1 (s m-1))]))
               #:env (list
                      (cons #'n #'Nat)
                      (cons #'m #'Nat)))
              (pt-decl
               #'n
               (list
                (pt-match
                 #'z
                 (pt-decl
                  #'m
                  (list
                   (pt-match
                    #'_
                    (pt-body #'z)))))
                (pt-match
                 #'(s n-110)
                 (pt-decl
                  #'m
                  (list
                   (pt-match
                    #'z
                    (pt-body #'(s n-110)))
                   (pt-match
                    #'(s m-111)
                    (pt-body #'(bad-minus n-110 (s m-111)))))))))))

  ; three match variable example
  (check-true
   (pt-equal?
    (create-pattern-tree #'((n m o)
                              ([z _ (s o-1) => z]
                               [(s n-1) z (s o-1) => (s n-1)]
                               [(s n-1) (s m-1) z => (bad-minus n-1 (s m-1))]))
                           #:env (list
                                  (cons #'n #'Nat)
                                  (cons #'m #'Nat)
                                  (cons #'o #'Nat)))
    (pt-decl
     #'n
     (list
      (pt-match
       #'z
       (pt-decl
        #'m
        (list
         (pt-match
          #'_
          (pt-decl
           #'o
           (list
            (pt-match
             #'(s o-112)
             (pt-body #'z))))))))
      (pt-match
       #'(s n-113)
       (pt-decl
        #'m
        (list
         (pt-match
          #'z
          (pt-decl
           #'o
           (list
            (pt-match
             #'(s o-114)
             (pt-body #'(s n-113))))))
         (pt-match
          #'(s m-115)
          (pt-decl
           #'o
           (list
            (pt-match
             #'z
             (pt-body #'(bad-minus n-113 (s m-115))))))))))))))

  ; lists
  (check-true
   (pt-equal?
    (create-pattern-tree #'((a b)
                              ([(nil _) (nil _) => true]
                               [(nil _) (cons _ _ _) => false]
                               [(cons _ _ _) (nil _) => false]
                               [(cons _ a rsta) (cons _ b rstb) => (and (f a b) (andmap2 A B f rsta rstb))]))
                           #:env
                           (list
                            (cons #'a #'(List Nat))
                            (cons #'b #'(List Nat))))
    (pt-decl
     #'a
     (list
      (pt-match
       #'(nil _16)
       (pt-decl
        #'b
        (list
         (pt-match
          #'(nil _17)
          (pt-body #'true))
         (pt-match
          #'(cons _18 _19 _20)
          (pt-body #'false)))))
      (pt-match
       #'(cons _21 _22 _23)
       (pt-decl
        #'b
        (list
         (pt-match
          #'(nil _24)
          (pt-body #'false))
         (pt-match
          #'(cons _25 b26 rstb27)
          (pt-body #'(and (f _22 b26) (andmap2 A B f _23 rstb27)))))))))))

  ; booleans
  (check-true
   (pt-equal? (create-pattern-tree #'((a b)
                                      ([true false => A]
                                       [x true => B]))
                                   #:env
                                   (list (cons #'b #'Bool)
                                         (cons #'a #'Bool)))
              (pt-decl
               #'a
               (list
                (pt-match
                 #'true
                 (pt-decl
                  #'b
                  (list
                   (pt-match
                    #'false
                    (pt-body #'A))
                   (pt-match
                    #'true
                    (pt-body #'B)))))
                (pt-match
                 #'x
                 (pt-decl
                  #'b
                  (list
                   (pt-match
                    #'true
                    (pt-body #'B)))))))))

  ;; ADDITIONAL NESTING
  (check-true
   (pt-equal?
    (create-pattern-tree #'((a b)
                            ([z z => A]
                             [(s (s (s b))) (s m) => b]))
                         #:env
                         (list
                          (cons #'a #'Nat)
                          (cons #'b #'Nat)))
    (pt-decl
     #'a
     (list
      (pt-match
       #'z
       (pt-decl
        #'b
        (list
         (pt-match
          #'z
          (pt-body #'A)))))
      (pt-match
       #'(s temp28) ; note: for use in binding, we need to resolve temp bindings before positional input variables
       (pt-decl     ; this means that we should effectively process temps by storing them on a stack, and processing in reverse
        #'temp28
        (list
         (pt-match
          #'(s temp29)
          (pt-decl
           #'temp29
           (list
            (pt-match
             #'(s b30)
             (pt-decl
              #'b
              (list
               (pt-match
                #'(s m31)
                (pt-body #'b30))))))))))))))) ; note that we use the temp b not the match variable

  (check-true
   (pt-equal?
    (create-pattern-tree
     #'((e1 e2)
        ([z z => A]
         [(s (s e2)) z => B]
         [(s (s e2)) (s m) => C]))
     #:env
     (list
      (cons #'e1 #'Nat)
      (cons #'e2 #'Nat)))
    (pt-decl
     #'e1
     (list
      (pt-match
       #'z
       (pt-decl
        #'e2
        (list
         (pt-match
          #'z
          (pt-body #'A)))))
      (pt-match
       #'(s temp32)
       (pt-decl
        #'temp32
        (list
         (pt-match
          #'(s e233)
          (pt-decl
           #'e2
           (list
            (pt-match
             #'z
             (pt-body #'B))
            (pt-match
             #'(s m34)
             (pt-body #'C))))))))))))

  ;; WITH AND WITHOUT TYPE CONTEXT
  ; effectively, z = _ = n in this scenario
  ; TODO PR103: Don't think this should pass as n is unbound.
  ; NOTE: Work around issue with tests relying on generated names.
  (begin (generate-temporary) (generate-temporary) (void))
  #;(check-true
   (pt-equal?
    (create-pattern-tree
     #'((n m)
        ([z z => z]
         [n _ => n]
         [(s n-1) (s m-1) => (minus n-1 m-1)])))
    (pt-decl
     #'n
     (list
      (pt-match
       #'(s n-135)
       (pt-decl
        #'m
        (list
         (pt-match
          #'(s m-136)
          (pt-body #'(minus n-135 m-136)))
         (pt-match
          #'z
          (pt-body #'n)))))
      (pt-match
       #'z
       (pt-decl
        #'m
        (list
         (pt-match
          #'z
          (pt-body #'n)))))))))

  (check-true
   (pt-equal?
    (create-pattern-tree
     #'((n m)
        ([z z => z]
         [n _ => n]
         [(s n-1) (s m-1) => (minus n-1 m-1)]))
     #:env
     (list (cons #'m #'Nat)
           (cons #'n #'Nat)))
    (pt-decl
     #'n
     (list
      (pt-match
       #'z
       (pt-decl
        #'m
        (list
         (pt-match
          #'z
          (pt-body #'z))
         (pt-match
          #'_
          (pt-body #'n)))))
      (pt-match
       #'(s n-137)
       (pt-decl
        #'m
        (list
         (pt-match
          #'(s m-138)
          (pt-body #'(minus n-137 m-138)))
         (pt-match
          #'_
          (pt-body #'n)))))
      (pt-match
       #'n
       (pt-decl
        #'m
        (list
         (pt-match
          #'_
          (pt-body #'n)))))))))

  ; complicated (bogus) nested example; note that we don't actually
  ; need to do semantic analysis when recompiling the pattern
  ; TODO PR103: Invalid test since e1 and e2 unbound.
  ; NOTE: Work around issue with tests relying on generated names.
  (begin
    (for ([i (in-range 0 38)])
      (generate-temporary))
    (void))
  #;(check-true
   (pt-equal?
    (create-pattern-tree #'((e1 e2)
                            ([(z a) (z b) => a]
                             [(s a b c d) (s c d) => c]
                             [(s (s a) x (s d) (s b)) (s c d) => b]
                             [(s (s a) x (s d) (s e f)) (s c d) => d]
                             [(s (s (s a)) x (s d) (s c)) (s c d) => (s a)])))
    (pt-decl
     #'e1
     (list
      (pt-match
       #'(z a39)
       (pt-decl
        #'e2
        (list
         (pt-match
          #'(z b40)
          (pt-body #'a39)))))
      (pt-match
       #'(s temp41 b44 temp42 temp43) ; note priority of temporary generation over pattern variables!
       (pt-decl
        #'temp41
        (list
         (pt-match
          #'(s temp45)
          (pt-decl
           #'temp45
           (list
            (pt-match
             #'(s a47) ; note: to accomodate for nested patterns, we need to explore the last case first
             (pt-decl  ; since it is the longest "non pattern variable"
              #'temp42
              (list
               (pt-match
                #'(s d48)
                (pt-decl
                 #'temp43
                 (list
                  (pt-match
                   #'(s c49)
                   (pt-decl
                    #'e2
                    (list
                     (pt-match
                      #'(s c50 d51)
                      (pt-body #'(s a47))))))
                  (pt-match
                   #'(s e52 f53)
                   (pt-decl
                    #'e2
                    (list
                     (pt-match
                      #'(s c54 d55)
                      (pt-body #'d48))))) ; propagated from inner pattern variable in (s a)
                  (pt-match
                   #'d
                   (pt-decl
                    #'e2
                    (list
                    (pt-match
                     #'(s c56 d57)
                     (pt-body #'temp42)))))))) ; propagated from outer pattern variable in a
               (pt-match
                #'c
                (pt-decl
                 #'temp43
                 (list
                  (pt-match
                   #'d
                   (pt-decl
                    #'e2
                    (list
                     (pt-match
                      #'(s c58 d59)
                      (pt-body #'temp42))))))))))) ; propagated from outer pattern variable in a
            (pt-match
             #'a
             (pt-decl
              #'temp42
              (list
               (pt-match
                #'(s d60)
                (pt-decl
                 #'temp43
                 (list
                  (pt-match
                   #'(s b61)
                   (pt-decl
                    #'e2
                    (list
                     (pt-match
                      #'(s c62 d63)
                      (pt-body #'b61)))))
                  (pt-match
                   #'(s e64 f65)
                   (pt-decl
                    #'e2
                    (list
                     (pt-match
                      #'(s c66 d67)
                      (pt-body #'d60)))))
                  (pt-match
                   #'d
                   (pt-decl
                    #'e2
                    (list
                     (pt-match
                      #'(s c68 d69)
                      (pt-body #'temp42)))))))) ; propagated from outer pattern variable a
               (pt-match
                #'c
                (pt-decl
                 #'temp43
                 (list
                  (pt-match
                   #'d
                   (pt-decl
                    #'e2
                    (list
                     (pt-match
                      #'(s c70 d71)
                      (pt-body #'temp42)))))))))))))) ; propagated from outer pattern variable a
         (pt-match
          #'a
          (pt-decl
           #'temp42
           (list
            (pt-match
             #'c
             (pt-decl
              #'temp43
              (list
               (pt-match
                #'d
                (pt-decl
                 #'e2
                 (list
                  (pt-match
                   #'(s c72 d73)
                   (pt-body #'temp42))))))))))))))))))

  ; TODO PR103: Invalid test since a unbound.
  #;(check-true
   (pt-equal?
    (create-pattern-tree #'((a)
                            ([x => A]
                             [(y (y b)) => b])))
    (pt-decl
     #'a
     (list
      (pt-match
       #'(y temp74)
       (pt-decl
        #'temp74
        (list
         (pt-match
          #'(y b76)
          (pt-body #'b76))
         (pt-match
          #'temp75
          (pt-body #'A)))))
      (pt-match
       #'x
       (pt-body #'A))))))

  ; type inference within nested types
  (check-true
   (pt-equal?
    (create-pattern-tree
      #'((n m)
         ([(nil T) z => A]
          [(cons T z (cons T (s (s x)) (cons T z (nil T)))) z => (cons T z x)]))
      #:env (list
             (cons #'n #'(List Nat))
             (cons #'m #'Nat)))
   (pt-decl
    #'n
    (list
     (pt-match
      #'(nil T77)
      (pt-decl
       #'m
       (list
        (pt-match
         #'z
         (pt-body #'A)))))
     (pt-match
      #'(cons T79 z temp78) ; important: should be z and not a temporary zNN for nested cases too!
      (pt-decl
       #'temp78
       (list
        (pt-match
         #'(cons T82 temp80 temp81)
         (pt-decl
          #'temp80
          (list
           (pt-match
            #'(s temp83)
            (pt-decl
             #'temp83
             (list
              (pt-match
               #'(s x84)
               (pt-decl
                #'temp81
                (list
                 (pt-match
                  #'(cons T86 z temp85)
                  (pt-decl
                   #'temp85
                   (list
                    (pt-match
                     #'(nil T87)
                     (pt-decl
                      #'m
                      (list
                       (pt-match
                        #'z
                        (pt-body #'(cons T79 z x84))))))))))))))))))))))))))