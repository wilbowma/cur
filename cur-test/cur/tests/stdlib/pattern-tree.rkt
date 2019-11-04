#lang cur
(require cur/stdlib/pattern-tree
         (for-syntax rackunit))

;; NESTED TREE TESTS

(begin-for-syntax
  
  (check-true
   (nested-equal? (create-nested-pattern #'((n m)
                                            ([z z => A]
                                             [z (s x) => B])))
                  (nested #'n
                          (list
                           (nested-match #'z
                                         (nested #'m
                                                 (list
                                                  (nested-match #'z
                                                                (nested-body #'A))
                                                  (nested-match #'(s x)
                                                                (nested-body #'B)))))))))

  (check-true
   (nested-equal? (create-nested-pattern #'((n m)
                                            ([z _ => z]
                                             [(s n-1) z => (s n-1)]
                                             [(s n-1) (s m-1) => (bad-minus n-1 (s m-1))])))
                  (nested #'n
                          (list
                           (nested-match #'z
                                         (nested #'m
                                                 (list
                                                  (nested-match #'_
                                                                (nested-body #'z)))))
                           (nested-match #'(s n-1)
                                         (nested #'m
                                                 (list
                                                  (nested-match #'z
                                                                (nested-body #'(s n-1)))
                                                  (nested-match #'(s m-1)
                                                                (nested-body #'(bad-minus n-1 (s m-1)))))))))))

  (check-true
   (nested-equal?
    (create-nested-pattern #'((n m o)
                              ([z _ (s o-1) => z]
                               [(s n-1) z (s o-1) => (s n-1)]
                               [(s n-1) (s m-1) z => (bad-minus n-1 (s m-1))])))
    (nested #'n
            (list
             (nested-match #'z
                           (nested #'m
                                   (list
                                    (nested-match #'_
                                                  (nested #'o
                                                          (list
                                                           (nested-match #'(s o-1)
                                                                         (nested-body #'z))))))))
             (nested-match #'(s n-1)
                           (nested #'m
                                   (list
                                    (nested-match #'z
                                                  (nested #'o
                                                          (list
                                                           (nested-match #'(s o-1)
                                                                         (nested-body #'(s n-1))))))
                                    (nested-match #'(s m-1)
                                                  (nested #'o
                                                          (list
                                                           (nested-match #'z
                                                                         (nested-body #'(bad-minus n-1 (s m-1))))))))))))))

  (check-true
   (nested-equal?
    (create-nested-pattern #'((a b)
                              ([(nil _) (nil _) => true]
                               [(nil _) (cons _ _ _) => false]
                               [(cons _ _ _) (nil _) => false]
                               [(cons _ a rsta) (cons _ b rstb) => (and (f a b) (andmap2 A B f rsta rstb))])))
    (nested #'a
            (list
             (nested-match #'(nil _)
                           (nested #'b
                                   (list
                                    (nested-match #'(nil _)
                                                  (nested-body #'true))
                                    (nested-match #'(cons _ _ _)
                                                  (nested-body #'false)))))
             (nested-match #'(cons _ a rsta) ; note pattern name, we may want to update this if more than one pattern
                           (nested #'b
                                   (list
                                    (nested-match #'(nil _)
                                                  (nested-body #'false))
                                    (nested-match #'(cons _ b rstb)
                                                  (nested-body #'(and (f a b) (andmap2 A B f rsta rstb)))))))))))

  ;; ADDITIONAL NESTING

  (check-true
   (nested-equal?
    (create-nested-pattern #'((e1 e2)
                              ([z z => A]
                               [(s (s e2)) (s m) => B])))
    (nested #'e1
            (list
             (nested-match #'z
                           (nested #'e2
                                   (list
                                    (nested-match #'z
                                                  (nested-body #'A)))))
             (nested-match #'(s temp1)
                           (nested #'temp1
                                   (list
                                    (nested-match #'(s e2)
                                                  (nested #'e2
                                                          (list
                                                           (nested-match #'(s m)
                                                                         (nested-body #'B))))))))))))
    
  (check-true
   (nested-equal?
    (create-nested-pattern
     #'((e1 e2)
        ([z z => A]
         [(s (s e2)) z => B]
         [(s (s e2)) (s m) => C])))
    (nested #'e1
            (list
             (nested-match #'z
                           (nested #'e2
                                   (list
                                    (nested-match #'z
                                                  (nested-body #'A)))))
             (nested-match #'(s temp2)
                           (nested #'temp2
                                   (list
                                    (nested-match #'(s e2)
                                                  (nested #'e2
                                                          (list
                                                           (nested-match #'z
                                                                         (nested-body #'B))
                                                           (nested-match #'(s m)
                                                                         (nested-body #'C))))))))))))

  (check-true
   (nested-equal?
    (create-nested-pattern #'((e1 e2)
                              ([z z => A]
                               [(s a b c d) (s c d) => B]
                               [(s (s a) x (s d) (s b)) (s c d) => C]
                               [(s (s a) x (s d) (s e f)) (s c d) => D]
                               [(s (s (s a)) x (s d) (s c)) (s c d) => E])))
    (nested #'e1
            (list
             (nested-match #'z
                           (nested #'e2
                                   (list
                                    (nested-match #'z
                                                  (nested-body #'A)))))
             (nested-match #'(s temp3 x temp4 temp5)
                           (nested #'temp3
                                   (list
                                    (nested-match #'a
                                                  (nested #'temp4
                                                          (list
                                                           (nested-match #'c
                                                                         (nested #'temp5
                                                                                 (list
                                                                                  (nested-match #'d
                                                                                                (nested #'e2
                                                                                                        (list
                                                                                                         (nested-match #'(s c d)
                                                                                                                       (nested-body #'B)))))))))))
                                    (nested-match #'(s temp6)
                                                  (nested #'temp6
                                                          (list
                                                           (nested-match #'a
                                                                         (nested #'temp4
                                                                                 (list
                                                                                  (nested-match #'(s d)
                                                                                                (nested #'temp5
                                                                                                        (list
                                                                                                         (nested-match #'(s b)
                                                                                                                       (nested #'e2
                                                                                                                               (list
                                                                                                                                (nested-match #'(s c d)
                                                                                                                                              (nested-body #'C)))))
                                                                                                         (nested-match #'(s e f)
                                                                                                                       (nested #'e2
                                                                                                                               (list
                                                                                                                                (nested-match #'(s c d)
                                                                                                                                              (nested-body #'D)))))))))))
                                                           (nested-match #'(s a)
                                                                         (nested #'temp4
                                                                                 (list
                                                                                  (nested-match #'(s d)
                                                                                                (nested #'temp5
                                                                                                        (list
                                                                                                         (nested-match #'(s c)
                                                                                                                       (nested #'e2
                                                                                                                               (list
                                                                                                                                (nested-match #'(s c d)
                                                                                                                                              (nested-body #' E))))))))))))))))))))))