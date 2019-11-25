#lang cur
(require cur/stdlib/pattern-tree
         cur/stdlib/bool
         cur/stdlib/nat
         (except-in cur/stdlib/list
                    cons)
         (for-syntax rackunit))

;; NESTED TREE TESTS

(begin-for-syntax
  
  (check-true
   (nested-equal? (create-nested-pattern #'((n m)
                                            ([z z => A]
                                             [z (s x) => B]))
                                         #:env (list
                                                (cons #'n #'Nat)
                                                (cons #'m #'Nat)))
                  (nested #'n
                          (list
                           (nested-match #'z
                                         (nested #'m
                                                 (list
                                                  (nested-match #'z
                                                                (nested-body #'A)
                                                                #f)
                                                  (nested-match #'(s x)
                                                                (nested-body #'B)
                                                                #f)))
                                         #f)))))

  ; body identifiers rebound
  (check-true
   (nested-equal? (create-nested-pattern #'((n)
                                            ([n => n]))
                                         #:env (list
                                                (cons #'n #'Nat)))
                  (nested #'n
                          (list
                           (nested-match #'n1
                                         (nested-body #'n1)
                                         #t)))))

  (check-true
   (nested-equal? (create-nested-pattern #'((n m)
                                            ([z _ => z]
                                             [(s n-1) z => (s n-1)]
                                             [(s n-1) (s m-1) => (bad-minus n-1 (s m-1))]))
                                         #:env (list
                                                (cons #'n #'Nat)
                                                (cons #'m #'Nat)))
                  (nested #'n
                          (list
                           (nested-match #'z
                                         (nested #'m
                                                 (list
                                                  (nested-match #'_2
                                                                (nested-body #'z)
                                                                #t)))
                                         #f)
                           (nested-match #'(s n-1)
                                         (nested #'m
                                                 (list
                                                  (nested-match #'z
                                                                (nested-body #'(s n-1))
                                                                #f)
                                                  (nested-match #'(s m-1)
                                                                (nested-body #'(bad-minus n-1 (s m-1)))
                                                                #f)))
                                         #f)))))

  (check-true
   (nested-equal?
    (create-nested-pattern #'((n m o)
                              ([z _ (s o-1) => z]
                               [(s n-1) z (s o-1) => (s n-1)]
                               [(s n-1) (s m-1) z => (bad-minus n-1 (s m-1))]))
                           #:env (list
                                  (cons #'n #'Nat)
                                  (cons #'m #'Nat)
                                  (cons #'o #'Nat)))
    (nested #'n
            (list
             (nested-match #'z
                           (nested #'m
                                   (list
                                    (nested-match #'_3
                                                  (nested #'o
                                                          (list
                                                           (nested-match #'(s o-1)
                                                                         (nested-body #'z)
                                                                         #f)))
                                                  #t)))
                           #f)
             (nested-match #'(s n-1)
                           (nested #'m
                                   (list
                                    (nested-match #'z
                                                  (nested #'o
                                                          (list
                                                           (nested-match #'(s o-1)
                                                                         (nested-body #'(s n-1))
                                                                         #f)))
                                                  #f)
                                    (nested-match #'(s m-1)
                                                  (nested #'o
                                                          (list
                                                           (nested-match #'z
                                                                         (nested-body #'(bad-minus n-1 (s m-1)))
                                                                         #f)))
                                                  #f)))
                           #f)))))

  (check-true
   (nested-equal?
    (create-nested-pattern #'((a b)
                              ([(nil _) (nil _) => true]
                               [(nil _) (cons _ _ _) => false]
                               [(cons _ _ _) (nil _) => false]
                               [(cons _ a rsta) (cons _ b rstb) => (and (f a b) (andmap2 A B f rsta rstb))]))
                           #:env
                           (list
                            (cons #'a #'(List Nat))
                            (cons #'b #'(List Nat))))
    (nested #'a
            (list
             (nested-match #'(nil _)
                           (nested #'b
                                   (list
                                    (nested-match #'(nil _)
                                                  (nested-body #'true)
                                                  #f)
                                    (nested-match #'(cons _ _ _)
                                                  (nested-body #'false)
                                                  #f)))
                           #f)
             (nested-match #'(cons _ a rsta) ; note pattern name is chosen to be the most specific one
                           (nested #'b
                                   (list
                                    (nested-match #'(nil _)
                                                  (nested-body #'false)
                                                  #f)
                                    (nested-match #'(cons _ b rstb)
                                                  (nested-body #'(and (f a b) (andmap2 A B f rsta rstb)))
                                                  #f)))
                           #f)))))

  ;; CONSTRUCTOR AND PATTERN VARIABLES
  (check-true
   (nested-equal? (create-nested-pattern #'((a b)
                                            ([true false => A]
                                             [x true => B]))
                                         #:env
                                         (list (cons #'b #'Bool)
                                               (cons #'a #'Bool)))
                  (nested #'a
                          (list
                           (nested-match #'true
                                         (nested #'b
                                                 (list
                                                  (nested-match #'false
                                                                (nested-body #'A)
                                                                #f)))
                                         #f)
                           (nested-match #'x4
                                         (nested #'b
                                                 (list
                                                  (nested-match #'true
                                                                (nested-body #'B)
                                                                #f)))
                                         #t)))))

  ;; ADDITIONAL NESTING
  (check-true
   (nested-equal?
    (create-nested-pattern #'((e1 e2)
                              ([z z => A]
                               [(s (s e2)) (s m) => B]))
                           #:env
                           (list
                            (cons #'e1 #'Nat)
                            (cons #'e2 #'Nat)))
    (nested #'e1
            (list
             (nested-match #'z
                           (nested #'e2
                                   (list
                                    (nested-match #'z
                                                  (nested-body #'A)
                                                  #f)))
                           #f)
             (nested-match #'(s temp5)
                           (nested #'temp5
                                   (list
                                    (nested-match #'(s e2)
                                                  (nested #'e2
                                                          (list
                                                           (nested-match #'(s m)
                                                                         (nested-body #'B)
                                                                         #f)))
                                                  #f)))
                           #f)))))
    
  (check-true
   (nested-equal?
    (create-nested-pattern
     #'((e1 e2)
        ([z z => A]
         [(s (s e2)) z => B]
         [(s (s e2)) (s m) => C]))
     #:env
     (list
      (cons #'e1 #'Nat)
      (cons #'e2 #'Nat)))
    (nested #'e1
            (list
             (nested-match #'z
                           (nested #'e2
                                   (list
                                    (nested-match #'z
                                                  (nested-body #'A)
                                                  #f)))
                           #f)
             (nested-match #'(s temp6)
                           (nested #'temp6
                                   (list
                                    (nested-match #'(s e2)
                                                  (nested #'e2
                                                          (list
                                                           (nested-match #'z
                                                                         (nested-body #'B)
                                                                         #f)
                                                           (nested-match #'(s m)
                                                                         (nested-body #'C)
                                                                         #f)))
                                                  #f)))
                           #f)))))

  ;; WITH AND WITHOUT TYPE CONTEXT
  ; effectively, z = _ = n in this scenario
  (check-true
   (nested-equal?
    (create-nested-pattern
     #'((n m)
        ([z z => z]
         [n _ => n]
         [(s n-1) (s m-1) => (minus n-1 m-1)])))
    (nested
     #'n
     (list
      (nested-match
       #'z7
       (nested
        #'m
        (list
         (nested-match
          #'z8
          (nested-body #'z7) ; note: bound to first occurrence
          #t)))
       #t)
      (nested-match
       #'(s n-1)
       (nested
        #'m
        (list
         (nested-match
          #'(s m-1)
          (nested-body #'(minus n-1 m-1))
          #f)))
       #f)))))
  
  (check-true
   (nested-equal?
    (create-nested-pattern
     #'((n m)
        ([z z => z]
         [n _ => n]
         [(s n-1) (s m-1) => (minus n-1 m-1)]))
     #:env
     (list (cons #'m #'Nat)
           (cons #'n #'Nat)))
    (nested
     #'n
     (list
      (nested-match
       #'z
       (nested
        #'m
        (list
         (nested-match
          #'z
          (nested-body #'z)
          #f)))
       #f)
      (nested-match
       #'n9
       (nested
        #'m
        (list
         (nested-match
          #'_10
          (nested-body #'n9)
          #t)))
       #t)
      (nested-match
       #'(s n-1)
       (nested
        #'m
        (list
         (nested-match
          #'(s m-1)
          (nested-body #'(minus n-1 m-1))
          #f)))
       #f)))))

  (check-true
   (nested-equal?
    (create-nested-pattern #'((e1 e2)
                              ([z z => z]
                               [(s a b c d) (s c d) => c]
                               [(s (s a) x (s d) (s b)) (s c d) => x]
                               [(s (s a) x (s d) (s e f)) (s c d) => d]
                               [(s (s (s a)) x (s d) (s c)) (s c d) => (s a)]))
                           #:env (list
                                  (cons #'e2 #'Nat)
                                  (cons #'e1 #'Nat)))
    (nested #'e1
            (list
             (nested-match #'z
                           (nested #'e2
                                   (list
                                    (nested-match #'z
                                                  (nested-body #'z)
                                                  #f)))
                           #f)
             (nested-match #'(s temp11 b temp12 temp13)
                           (nested #'temp11
                                   (list
                                    (nested-match #'a14
                                                  (nested #'temp12
                                                          (list
                                                           (nested-match #'c15
                                                                         (nested #'temp13
                                                                                 (list
                                                                                  (nested-match #'d16
                                                                                                (nested #'e2
                                                                                                        (list
                                                                                                         (nested-match #'(s c d)
                                                                                                                       (nested-body #'c15)
                                                                                                                       #f)))
                                                                                                #t)))
                                                                         #t)))
                                                  #t)
                                    (nested-match #'(s temp17)
                                                  (nested #'temp17
                                                          (list
                                                           (nested-match #'a18
                                                                         (nested #'temp12
                                                                                 (list
                                                                                  (nested-match #'(s d)
                                                                                                (nested #'temp13
                                                                                                        (list
                                                                                                         (nested-match #'(s b)
                                                                                                                       (nested #'e2
                                                                                                                               (list
                                                                                                                                (nested-match #'(s c d)
                                                                                                                                              (nested-body #'x)
                                                                                                                                              #f)))
                                                                                                                       #f)
                                                                                                         (nested-match #'(s e f)
                                                                                                                       (nested #'e2
                                                                                                                               (list
                                                                                                                                (nested-match #'(s c d)
                                                                                                                                              (nested-body #'d)
                                                                                                                                              #f)))
                                                                                                                       #f)))
                                                                                                #f)))
                                                                         #t)
                                                           (nested-match #'(s a)
                                                                         (nested #'temp12
                                                                                 (list
                                                                                  (nested-match #'(s d)
                                                                                                (nested #'temp13
                                                                                                        (list
                                                                                                         (nested-match #'(s c)
                                                                                                                       (nested #'e2
                                                                                                                               (list
                                                                                                                                (nested-match #'(s c d)
                                                                                                                                              (nested-body #'(s a))
                                                                                                                                              #f)))
                                                                                                                       #f)))
                                                                                                #t)))
                                                                         #f)))
                                                  #f)))
                           #f))))))
