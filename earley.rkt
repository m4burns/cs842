#lang racket

(require parser-tools/yacc
         parser-tools/lex)

(require (for-syntax racket/base
                     syntax/boundmap
                     parser-tools/private-lex/token-syntax))

(provide earley-parser)

(define-syntax (earley-parser stx)
  (syntax-case stx ()
    [(_ clause ...)
     (let ([clauses (syntax->list #'(clause ...))])
       (let-values ([(start grammar cfg-error parser-clauses src-pos?)
                     (let ([all-toks (apply
                                      append
                                      (map (lambda (clause)
                                             (syntax-case clause (tokens)
                                               [(tokens t ...)
                                                (apply
                                                 append
                                                 (map (lambda (t)
                                                        (let ([v (syntax-local-value t (lambda () #f))])
                                                          (cond
                                                            [(terminals-def? v)
                                                             (map (lambda (v)
                                                                    (cons v #f))
                                                                  (syntax->list (terminals-def-t v)))]
                                                            [(e-terminals-def? v)
                                                             (map (lambda (v)
                                                                    (cons v #t))
                                                                  (syntax->list (e-terminals-def-t v)))]
                                                            [else null])))
                                                      (syntax->list #'(t ...))))]
                                               [_else null]))
                                           clauses))]
                           [all-end-toks (apply
                                          append
                                          (map (lambda (clause)
                                                 (syntax-case clause (end)
                                                   [(end t ...)
                                                    (syntax->list #'(t ...))]
                                                   [_else null]))
                                               clauses))])
                       (let loop ([clauses clauses]
                                  [cfg-start #f]
                                  [cfg-grammar #f]
                                  [cfg-error #f]
                                  [src-pos? #f]
                                  [parser-clauses null])
                         (if (null? clauses)
                             (values cfg-start
                                     cfg-grammar
                                     cfg-error
                                     (reverse parser-clauses)
                                     src-pos?)
                             (syntax-case (car clauses) (start error grammar src-pos)
                               [(start tok)
                                (loop (cdr clauses) #'tok cfg-grammar cfg-error src-pos? parser-clauses)]
                               [(error expr)
                                (loop (cdr clauses) cfg-start cfg-grammar #'expr src-pos? parser-clauses)]
                               [(grammar [nt [pat handle0 handle ...] ...] ...)
                                (let ([nts (make-bound-identifier-mapping)]
                                      [toks (make-token-identifier-mapping)]
                                      [end-toks (make-token-identifier-mapping)]
                                      [nt-ids (syntax->list #'(nt ...))]
                                      [patss (map (lambda (stx)
                                                    (map syntax->list (syntax->list stx)))
                                                  (syntax->list #'((pat ...) ...)))])
                                  ;; do this in a less silly way
                                  (for-each (lambda (nt)
                                              (bound-identifier-mapping-put! nts nt (list 0)))
                                            nt-ids)
                                  (for-each (lambda (t)
                                              (token-identifier-mapping-put! end-toks t #t))
                                            all-end-toks)
                                  (for-each (lambda (t)
                                              (unless (token-identifier-mapping-get end-toks (car t) (lambda () #f))
                                                (let ([id (gensym (syntax-e (car t)))])
                                                  (token-identifier-mapping-put! toks (car t)
                                                                                 (cons id (cdr t))))))
                                            all-toks)
                                        cfg-start
                                        cfg-grammar
                                  ;; Put all this stuff into some kind of structure:
                                        cfg-error
                                        src-pos?
                                        parser-clauses)]
                               [(grammar . _)
                                (raise-syntax-error
                                 #f
                                 "bad grammar clause"
                                 stx
                                 (car clauses))]
                               [(src-pos)
                                (loop (cdr clauses)
                                      cfg-start
                                      cfg-grammar
                                      cfg-error
                                      #t
                                      (cons (car clauses) parser-clauses))]
                               [_else
                                (loop (cdr clauses)
                                      cfg-start
                                      cfg-grammar
                                      cfg-error
                                      src-pos?
                                      (cons (car clauses) parser-clauses))]))))])
         #`(let ([orig-parse (parser
                              [error (lambda (a b c)
                                       (error 'cfg-parser "unexpected ~a token: ~a" b c))]
                              . #,parser-clauses)]
                 [error-proc #,cfg-error])

             ;; do some more stuff here

;; Tests.
(module* test racket/base
  (require (submod "..")
           parser-tools/lex
           racket/block
           racket/generator
           rackunit)

  ;; Test: parsing regular expressions.
  ;; Here is a test case on locations:
  (block
   (define-tokens regexp-tokens (ANCHOR STAR OR LIT LPAREN RPAREN EOF))
   (define lex (lexer-src-pos ["|" (token-OR lexeme)]
                              ["^" (token-ANCHOR lexeme)]
                              ["*" (token-STAR lexeme)]
                              [(repetition 1 +inf.0 alphabetic) (token-LIT lexeme)]
                              ["(" (token-LPAREN lexeme)]
                              [")" (token-RPAREN lexeme)]
                              [whitespace (return-without-pos (lex input-port))]
                              [(eof) (token-EOF 'eof)]))
   (define -parse (cfg-parser
                   (tokens regexp-tokens)
                   (start top)
                   (end EOF)
                   (src-pos)
                   (grammar [top [(maybe-anchor regexp)
                                  (cond [$1
                                         `(anchored ,$2 ,(pos->sexp $1-start-pos) ,(pos->sexp $2-end-pos))]
                                        [else
                                         `(unanchored ,$2 ,(pos->sexp $1-start-pos) ,(pos->sexp $2-end-pos))])]]
                            [maybe-anchor [(ANCHOR) #t]
                                          [() #f]]
                            [regexp [(regexp STAR) `(star ,$1 ,(pos->sexp $1-start-pos) ,(pos->sexp $2-end-pos))]
                                    [(regexp OR regexp) `(or ,$1 ,$3 ,(pos->sexp $1-start-pos) ,(pos->sexp $3-end-pos))]
                                    [(LPAREN regexp RPAREN) `(group ,$2 ,(pos->sexp $1-start-pos) ,(pos->sexp $3-end-pos))]
                                    [(LIT) `(lit ,$1 ,(pos->sexp $1-start-pos) ,(pos->sexp $1-end-pos))]])))
   (define (pos->sexp pos)
     (position-offset pos))

   (define (parse s)
     (define ip (open-input-string s))
     (port-count-lines! ip)
     (-parse (lambda () (lex ip))))

   (check-equal? (parse "abc")
                 '(unanchored (lit "abc" 1 4) 1 4))
   (check-equal? (parse "a | (b*) | c")
                 '(unanchored (or (or (lit "a" 1 2)
                                      (group (star (lit "b" 6 7) 6 8) 5 9)
                                      1 9)
                                  (lit "c" 12 13)
                                  1 13)
                              1 13)))


  ;; Check that cfg-parser can accept error functions of 3 arguments:
  (block
   (define-tokens non-terminals (ONE ZERO EOF))
   (define parse
     (cfg-parser (tokens non-terminals)
                 (start ones)
                 (end EOF)
                 (error (lambda (tok-ok tok-name tok-val)
                          (error (format "~a ~a ~a" tok-ok tok-name tok-val))))
                 (grammar [ones [() null]
                                [(ONE ones) (cons $1 $2)]])))
   (define (sequence->tokenizer s)
     (define-values (more? next) (sequence-generate s))
     (lambda ()
       (cond [(more?) (next)]
             [else (token-EOF 'eof)])))
   (check-exn #rx"#t ZERO zero"
              (lambda () (parse (sequence->tokenizer (list (token-ZERO "zero")))))))




  ;; Check that cfg-parser can accept error functions of 5 arguments:
  (block
   (define-tokens non-terminals (ONE ZERO EOF))
   (define parse
     (cfg-parser (tokens non-terminals)
                 (start ones)
                 (src-pos)
                 (end EOF)
                 (error (lambda (tok-ok tok-name tok-val start-pos end-pos)
                          (error (format "~a ~a ~a ~a ~a"
                                         tok-ok tok-name tok-val
                                         (position-offset start-pos)
                                         (position-offset end-pos)))))
                 (grammar [ones [() null]
                                [(ONE ones) (cons $1 $2)]])))
   (define (sequence->tokenizer s)
     (define-values (more? next) (sequence-generate s))
     (lambda ()
       (cond [(more?) (next)]
             [else (position-token (token-EOF 'eof)
                                   (position #f #f #f)
                                   (position #f #f #f))])))
   (check-exn #rx"#t ZERO zero 2 3"
              (lambda ()
                (parse
                 (sequence->tokenizer
                  (list (position-token
                         (token-ZERO "zero")
                         (position 2 2 5)
                         (position 3 2 6))))))))





  ;; Tests used during development
  (define-tokens non-terminals (PLUS MINUS STAR BAR COLON EOF))

  (define lex
    (lexer
     ["+" (token-PLUS '+)]
     ["-" (token-MINUS '-)]
     ["*" (token-STAR '*)]
     ["|" (token-BAR '||)]
     [":" (token-COLON '|:|)]
     [whitespace (lex input-port)]
     [(eof) (token-EOF 'eof)]))

  (define parse
    (cfg-parser
     (tokens non-terminals)
     (start <program>)
     (end EOF)
     (error (lambda (a b stx)
              (error 'parse "failed at ~s" stx)))
     (grammar [<program> [(PLUS) "plus"]
                         [(<minus-program> BAR <minus-program>) (list $1 $2 $3)]
                         [(<program> COLON) (list $1)]]
              [<minus-program> [(MINUS) "minus"]
                               [(<program> STAR) (cons $1 $2)]]
              [<simple> [(<alts> <alts> <alts> MINUS) "yes"]]
              [<alts> [(PLUS) 'plus]
                      [(MINUS) 'minus]]
              [<random> [() '0]
                        [(<random> PLUS) (add1 $1)]
                        [(<random> PLUS) (add1 $1)]])))

  (let ([p (open-input-string #;"+*|-|-*|+**" #;"-|+*|+**"
                              #;"+*|+**|-" #;"-|-*|-|-*"
                              #;"-|-*|-|-**|-|-*|-|-**"
                              "-|-*|-|-**|-|-*|-|-***|-|-*|-|-**|-|-*|-|-****|-|-*|-|-**|-|-*|-|-***
               |-|-*|-|-**|-|-*|-|-*****|-|-*|-|-**|-|-*|-|-***|-|-*|-|-**|-|-*|-|-****|
               -|-*|-|-**|-|-*|-|-***|-|-*|-|-**|-|-*|-|-*****"
                              ;; This one fails:
                              #;"+*")])
    (check-equal? (parse (lambda () (lex p)))
                  '((((((((((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *) || (((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *)) . *)
                        ||
                        (((((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *) || (((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *)) . *))
                       .
                       *)
                      ||
                      (((((((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *) || (((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *)) . *)
                        ||
                        (((((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *) || (((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *)) . *))
                       .
                       *))
                     .
                     *)
                    ||
                    (((((((((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *) || (((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *)) . *)
                        ||
                        (((((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *) || (((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *)) . *))
                       .
                       *)
                      ||
                      (((((((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *) || (((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *)) . *)
                        ||
                        (((((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *) || (((("minus" || "minus") . *) || (("minus" || "minus") . *)) . *)) . *))
                       .
                       *))
                     .
                     *)))))
