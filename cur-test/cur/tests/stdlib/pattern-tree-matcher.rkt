#lang cur
(require cur/stdlib/pattern-tree
         cur/stdlib/nat
         (except-in cur/stdlib/list
                    cons)
         (for-syntax rackunit))

(begin-for-syntax
  ; simple 1
  (check-equal?
   (syntax->datum
    (match (list #'z #'z)
     (create-pattern-tree
      #'((n m)
         ([z z => A]
          [z (s x) => B]))
      #:env (list
             (cons #'n #'Nat)
             (cons #'m #'Nat)))))
   'A)

  ; simple 2
  (check-equal?
   (syntax->datum
    (match (list #'z #'(s B))
     (create-pattern-tree
      #'((n m)
         ([z z => A]
          [z (s x) => x]))
      #:env (list
             (cons #'n #'Nat)
             (cons #'m #'Nat)))))
   'B)

  ; simple 3
  (check-equal?
   (syntax->datum
    (match (list #'z #'(s B))
     (create-pattern-tree
      #'((n m)
         ([z z => A]
          [z (s x) => (s (s x))]))
      #:env (list
             (cons #'n #'Nat)
             (cons #'m #'Nat)))))
   '(s (s B)))

  ; pattern variable 1
  (check-equal?
   (syntax->datum
    (match (list #'(s C) #'z)
     (create-pattern-tree
      #'((n m)
         ([z z => A]
          [z (s x) => x]
          [a z => a]))
      #:env (list
             (cons #'n #'Nat)
             (cons #'m #'Nat)))))
   '(s C))

  ; pattern variable 2
  (check-equal?
   (syntax->datum
    (match (list #'(s C) #'z)
     (create-pattern-tree
      #'((n m)
         ([z z => A]
          [(s x) (s x) => x]
          [a b => b]))
      #:env (list
             (cons #'n #'Nat)
             (cons #'m #'Nat)))))
   'z)

  ; nested 1
  (check-equal?
   (syntax->datum
    (match (list #'(s (s C)) #'z)
     (create-pattern-tree
      #'((n m)
         ([z z => A]
          [(s (s x)) z => x]))
      #:env (list
             (cons #'n #'Nat)
             (cons #'m #'Nat)))))
   'C)

  ; nested 2
  (check-equal?
   (syntax->datum
    (match (list #'(cons Nat z (cons Nat (s (s (cons A B C))) (cons Nat z (nil Nat)))) #'z)
     (create-pattern-tree
      #'((n m)
         ([(nil T) z => A]
          [(cons T z (cons T (s (s x)) (cons T z (nil T)))) z => (cons T z x)]))
      #:env (list
             (cons #'n #'(List Nat))
             (cons #'m #'Nat)))))
   '(cons Nat z (cons A B C))))