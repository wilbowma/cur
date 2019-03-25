#lang s-exp cur/curnel/turnstile-impl/dep-ind-cur2
(require cur/curnel/turnstile-impl/dep-ind-cur2+bool
         (submod cur/curnel/turnstile-impl/dep-ind-cur2+bool tauto)
         cur/curnel/turnstile-impl/dep-ind-cur2+sugar
         rackunit/turnstile)

(check-type False : Type)
(check-type True : Type)
(check-type I : True)
(check-type (And True False) : Type)

(check-type (conj True True I I) : (And True True))

(check-type (or_introL True False I) : (Or True False))
(check-type (or_introL True True I) : (Or True True))
(typecheck-fail (or_introL False True I) #:with-msg "expected.*False.*given.*True")
(check-type (or_introR False True I) : (Or False True))
(check-type (or_introR True True I) : (Or True True))
(typecheck-fail (or_introR True False I) #:with-msg "expected.*False.*given.*True")

(check-type (tauto True) : True)
(check-type (tauto (And True True)) : (And True True))
(typecheck-fail (tauto (And False True)) #:with-msg "no proof")
(typecheck-fail (tauto (And True False)) #:with-msg "no proof")
(typecheck-fail (tauto (And False False)) #:with-msg "no proof")

(check-type (tauto (Or True False)) : (Or True False))
(check-type (tauto (Or False True)) : (Or False True))
(typecheck-fail (tauto (Or False False)) #:with-msg "no proof")
