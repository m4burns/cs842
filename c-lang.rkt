#lang racket
(require parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         parser-tools/cfg-parser)

(define-lex-abbrevs
  (D (:/ #\0 #\9))
  (L (:or (:/ #\a #\z #\A #\Z) #\_))
  (H (:or D (:/ #\a #\f #\A #\F)))
  (E (:: (:or #\e #\E) (:? (:or #\+ #\-)) (:+ D)))
  (FS (:or #\f #\F #\l #\L))
  (IS (:* (:or #\u #\U #\l #\L))))

(struct c-token (kind lexeme start end) #:transparent)

(define-tokens c-const-tokens
  (char-const int-const float-const))
(define-tokens c-literal-tokens
  (id lbrace rbrace lbrack rbrack lparen rparen string
      ... >>= <<= += -= *= /= %= &= ^= or= >> << ++ --
      -> && oror <= >= == != semi comma op. & ! ~ - + *
      / % < > ^ or ? : =))
(define-tokens c-keyword-tokens
  (key-auto key-break key-case key-char key-const
            key-continue key-default key-do key-double
            key-else key-enum key-extern key-float
            key-for key-goto key-if key-inline key-int
            key-long key-register key-restrict key-return
            key-short key-signed key-sizeof key-static
            key-struct key-switch key-typedef key-union
            key-unsigned key-void key-volatile key-while
            key-_Bool key-_Complex key-_Imaginary))

(define (lex-c-source in)
  (define (unescape-string str)
    (regexp-replaces str
                     `([#rx"\\\\\\\\" "\\\\"]
                       [#rx"\\\\'" "'"]
                       [#rx"\\\\\"" "\""]
                       [#px"\\\\([0-7]{1,3})"
                        ,(lambda(_ dgts)
                           (string (integer->char (string->number dgts 8))))]
                       [#px"\\\\x([0-9a-fA-F]{1,4})"
                        ,(lambda(_ dgts)
                           (string (integer->char (string->number dgts 16))))]
                       [#rx"\\\\([abfnrtv])"
                        ,(lambda(_ u)
                           (string
                            (integer->char
                             (match u
                               ["a" #x07]
                               ["b" #x08]
                               ["f" #x0c]
                               ["n" #x0a]
                               ["r" #x0d]
                               ["t" #x09]
                               ["v" #x0b]))))])))
  (define (int-traits t)
    (match t
      [(and (regexp #rx"[uU]") (regexp #rx"[lL]")) 'const:int:long:unsigned]
      [(regexp #rx"[uU]") 'const:int:unsigned]
      [(regexp #rx"[lL]") 'const:int:long]
      [else 'const:int]))
  (define (float-traits t)
    (match t
      [(regexp #rx"[fF]") 'const:float]
      [(regexp #rx"[lL]") 'const:double:long]
      [else 'const:double]))
  (define-syntax (ret stx)
    (syntax-case stx ()
      [(_ kind)
       (if (pair? (cadr (syntax->datum stx)))
           #'(c-token kind lexeme start-pos end-pos)
           #'(kind (c-token (quote kind) lexeme start-pos end-pos)))]))
  (define c-lexer
    (lexer
     [(:: "/*" (complement (:: any-string "*/" any-string)) "*/") (ret 'comment)]
     [(:: L (:* (:or L D))) (ret 'id)]
     [(:: #\0 (:or #\x #\X) (:+ H) (:? IS)) (ret 'const:hex)]
     [(:: #\0 (:+ D) (:? IS)) (ret 'const:oct)]
     [(:: (:+ D) (:? IS)) (ret 'const:dec)]
     [(:: (:? L) #\' (:+ (:or (:: "\\" (:~)) (:~ #\'))) #\') (ret 'const:char)]
     [(:: (:+ D) E (:? FS)) (ret 'const:float)]
     [(:: (:* D) #\. (:+ D) (:? E) (:? FS)) (ret 'const:float)]
     [(:: (:+ D) #\. (:* D) (:? E) (:? FS)) (ret 'const:float)]
     [(:: (:? L) #\" (:* (:or (:: "\\" (:~)) (:~ #\"))) #\") (ret 'string)]
     ["..." (ret token-...)]
     [">>=" (ret token->>=)]
     ["<<=" (ret token-<<=)]
     ["+=" (ret token-+=)]
     ["-=" (ret token--=)]
     ["*=" (ret token-*=)]
     ["/=" (ret token-/=)]
     ["%=" (ret token-%=)]
     ["&=" (ret token-&=)]
     ["^=" (ret token-^=)]
     ["|=" (ret token-or=)]
     [">>" (ret token->>)]
     ["<<" (ret token-<<)]
     ["++" (ret token-++)]
     ["--" (ret token---)]
     ["->" (ret token-->)]
     ["&&" (ret token-&&)]
     ["||" (ret token-oror)]
     ["<=" (ret token-<=)]
     [">=" (ret token->=)]
     ["==" (ret token-==)]
     ["!=" (ret token-!=)]
     [";" (ret token-semi)]
     [(:or "{" "<%") (ret token-lbrace)]
     [(:or "}" "%>") (ret token-rbrace)]
     ["," (ret token-comma)]
     [":" (ret token-:)]
     ["=" (ret token-=)]
     ["(" (ret token-lparen)]
     [")" (ret token-rparen)]
     [(:or "[" "<:") (ret token-lbrack)]
     [(:or ")]" ":>") (ret token-rbrack)]
     ["." (ret token-op.)]
     ["&" (ret token-&)]
     ["!" (ret token-!)]
     ["~" (ret token-~)]
     ["-" (ret token--)]
     ["+" (ret token-+)]
     ["*" (ret token-*)]
     ["/" (ret token-/)]
     ["%" (ret token-%)]
     ["<" (ret token-<)]
     [">" (ret token->)]
     ["^" (ret token-^)]
     ["|" (ret token-or)]
     ["?" (ret token-?)]
     [whitespace (ret 'whitespace)]
     [(:~) (ret 'invalid)]
     [(eof) 'eof]))
  (filter-map
   (match-lambda
     [(or (c-token 'whitespace l s e)
          (c-token 'invalid l s e)
          (c-token 'comment l s e)) #f]
     [(c-token 'id l s e)
      ((match l
         ["auto" token-key-auto]
         ["break" token-key-break]
         ["case" token-key-case]
         ["char" token-key-char]
         ["const" token-key-const]
         ["continue" token-key-continue]
         ["default" token-key-default]
         ["do" token-key-do]
         ["double" token-key-double]
         ["else" token-key-else]
         ["enum" token-key-enum]
         ["extern" token-key-extern]
         ["float" token-key-float]
         ["for" token-key-for]
         ["goto" token-key-goto]
         ["if" token-key-if]
         ["inline" token-key-inline]
         ["int" token-key-int]
         ["long" token-key-long]
         ["register" token-key-register]
         ["restrict" token-key-restrict]
         ["return" token-key-return]
         ["short" token-key-short]
         ["signed" token-key-signed]
         ["sizeof" token-key-sizeof]
         ["static" token-key-static]
         ["struct" token-key-struct]
         ["switch" token-key-switch]
         ["typedef" token-key-typedef]
         ["union" token-key-union]
         ["unsigned" token-key-unsigned]
         ["void" token-key-void]
         ["volatile" token-key-volatile]
         ["while" token-key-while]
         ["_Bool" token-key-_Bool]
         ["_Complex" token-key-_Complex]
         ["_Imaginary" token-key-_Imaginary]
         [else token-id])
       (c-token 'id l s e))]
     [(c-token (and k (or 'string 'const:char)) l s e)
      (define ll (unescape-string (substring l 1 (sub1 (string-length l)))))
      (case k
        [(string) (token-string (c-token 'token-string ll s e))]
        [(const:char) (token-char-const (c-token 'token-char-const ll s e))])]
     [(c-token (and r (or 'const:hex 'const:oct 'const:dec))
               (regexp #rx"0?[xX]?([0-9]*)([uUlL]*)" (list _ m t))
               s e)
      (token-int-const
       (c-token (int-traits t)
                (string->number m
                                (match r
                                  ['const:hex 16]
                                  ['const:oct 8]
                                  ['const:dec 10]))
                s e))]
     [(c-token 'const:float (regexp #rx"([^fFlL]*)([fFlL]?)" (list _ m t)) s e)
      (token-float-const
       (c-token (float-traits t)
                (string->number m 10)
                s e))]
     [(var x) x])
   (let loop ()
     (define next-tok (c-lexer in))
     (if (eq? next-tok 'eof)
         empty
         (cons next-tok (loop))))))

(struct cstx-subscript (expr sub))
(struct cstx-funcall (expr args))
(struct cstx-op. (expr id))
(struct cstx-op-> (expr id))
(struct cstx-preinc (expr))
(struct cstx-postinc (expr))
(struct cstx-predec (expr))
(struct cstx-postdec (expr))
(struct cstx-postfix-init (typename inits))
(struct cstx-unary-op (op expr))
(struct cstx-sizeof (expr))
(struct cstx-cast (type expr))
(struct cstx-binary-op (op lhs rhs))
(struct cstx-cond-op (test lhs rhs))
(struct cstx-assign-op (op lhs rhs))
(struct cstx-decl (spec decls))

(define (parse-c-source toks)
  (define c-parser
    (cfg-parser
     (grammar
      ;; expressions
      (constant
       ((char-const) $1)
       ((int-const) $1)
       ((float-const) $1))
      (primary-expression
       ((id) $1)
       ((constant) $1)
       ((string) $1)
       ((lparen expression rparen) $2))
      (postfix-expression
       ((primary-expression) $1)
       ((postfix-expression lbrack expression rbrack) (cstx-subscript $1 $3))
       ((postfix-expression lparen argument-expression-list rparen) (cstx-funcall $1 (reverse $3)))
       ((postfix-expression op. id) (cstx-op. $1 $3))
       ((postfix-expression -> id) (cstx-op-> $1 $3))
       ((postfix-expression ++) (cstx-postinc $1))
       ((postfix-expression --) (cstx-postdec $1))
       ((lparen type-name rparen lbrace initializer-list rbrace) (cstx-postfix-init $2 (reverse $5))))
      (argument-expression-list
       ((assignment-expression) (list $1))
       ((argument-expression-list comma assignment-expression) (cons $3 $1)))
      (unary-expression
       ((postfix-expression) $1)
       ((++ postfix-expression) (cstx-preinc $2))
       ((-- postfix-expression) (cstx-predec $2))
       ((unary-operator cast-expression) (cstx-unary-op $1 $2))
       ((key-sizeof unary-expression) (cstx-sizeof $2))
       ((key-sizeof lparen type-name rparen) (cstx-sizeof $3)))
      (unary-operator
       ((&) '&) ((*) '*) ((+) '+) ((-) '-) ((~) '~) ((!) '!))
      (cast-expression
       ((unary-expression) $1)
       ((lparen type-name rparen cast-expression) (cstx-cast $2 $4)))
      (multiplicative-expression
       ((cast-expression) $1)
       ((multiplicative-expression * cast-expression) (cstx-binary-op '* $1 $3))
       ((multiplicative-expression / cast-expression) (cstx-binary-op '/ $1 $3))
       ((multiplicative-expression % cast-expression) (cstx-binary-op '% $1 $3)))
      (additive-expression
       ((multiplicative-expression) $1)
       ((additive-expression + multiplicative-expression) (cstx-binary-op '+ $1 $3))
       ((additive-expression - multiplicative-expression) (cstx-binary-op '- $1 $3)))
      (shift-expression
       ((additive-expression) $1)
       ((shift-expression << additive-expression) (cstx-binary-op '<< $1 $3))
       ((shift-expression >> additive-expression) (cstx-binary-op '>> $1 $3)))
      (relational-expression
       ((shift-expression) $1)
       ((relational-expression < shift-expression) (cstx-binary-op '< $1 $3))
       ((relational-expression > shift-expression) (cstx-binary-op '> $1 $3))
       ((relational-expression <= shift-expression) (cstx-binary-op '<= $1 $3))
       ((relational-expression >= shift-expression) (cstx-binary-op '>= $1 $3)))
      (equality-expression
       ((relational-expression) $1)
       ((equality-expression == relational-expression) (cstx-binary-op '== $1 $3))
       ((equality-expression != relational-expression) (cstx-binary-op '!= $1 $3)))
      (AND-expression
       ((equality-expression) $1)
       ((AND-expression & equality-expression) (cstx-binary-op '& $1 $3)))
      (exclusive-OR-expression
       ((AND-expression) $1)
       ((exclusive-OR-expression ^ AND-expression) (cstx-binary-op '^ $1 $3)))
      (inclusive-OR-expression
       ((exclusive-OR-expression) $1)
       ((inclusive-OR-expression or exclusive-OR-expression) (cstx-binary-op 'or $1 $3)))
      (logical-AND-expression
       ((inclusive-OR-expression) $1)
       ((logical-AND-expression && inclusive-OR-expression) (cstx-binary-op '&& $1 $3)))
      (logical-OR-expression
       ((logical-AND-expression) $1)
       ((logical-OR-expression oror logical-AND-expression) (cstx-binary-op 'oror $1 $3)))
      (conditional-expression
       ((logical-OR-expression) $1)
       ((logical-OR-expression ? expression : conditional-expression) (cstx-cond-op $1 $3 $5)))
      (assignment-expression
       ((conditional-expression) $1)
       ((unary-expression assignment-operator assignment-expression) (cstx-assign-op $2 $1 $3)))
      (assignment-operator
       ((=) '=) ((*=) '*=) ((/=) '/=) ((%=) '%=) ((+=) '+=) ((-=) '-=)
       ((<<=) '<<=) ((>>=) '>>=) ((&=) '&=) ((^=) '^=) ((or=) 'or=))
      (expression
       ((assignment-expression) (list $1))
       ((expression comma assignment-expression) (cons $3 $1)))
      (constant-expression
       ((conditional-expression) $1))
      ;; declarations
      (declaration
       ((declaration-specifiers init-declarator-list semi) (cstx-decl $1 $2)))
      (declaration-specifiers
       ;; page 411
       
                                                         
     (tokens c-const-tokens
             c-literal-tokens
             c-keyword-tokens)
     (start ???)
     (end ???)
     (error ???)))
  (void))

(pretty-print (lex-c-source (current-input-port)))
    