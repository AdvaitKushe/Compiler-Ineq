#lang racket
(provide (all-defined-out))
(require "ast.rkt" "types.rkt" "compile-ops.rkt" a86/ast)

;; Registers used
(define rax 'rax) ; return
(define rbx 'rbx) ; heap
(define rsp 'rsp) ; stack
(define rdi 'rdi) ; arg
(define r15 'r15) ; stack pad (non-volatile)

;; type CEnv = (Listof [Maybe Id])
  
;; Prog -> Asm
(define (compile p)
  (match p
    [(Prog ds e)
     (let ( (reg-val (gensym 'reg))  (is-val (gensym 'val))) 
          (prog (externs)
           (Global 'entry)
           (Label 'entry)
           (Push rbx)    ; save callee-saved register
           (Push r15)
           (Mov rbx rdi) ; recv heap pointer
           (compile-e e '())
           ; Create and return unary vector holding the result

          (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Je is-val)

          (Mov r8 1)
          (Mov (Offset rbx 0) r8)   ; write size of vector, 1
          (Mov (Offset rbx 8) rax)  ; write rax as single element of vector
          (Mov rax rbx)             ; return the pointer to the vector
          (Jmp reg-val)

          (Label is-val)
          (Xor rax type-val)

          (Label reg-val)
           (Pop r15)     ; restore callee-save register
           (Pop rbx)
           (Ret)
           (compile-defines ds)
           (Label 'raise_error_align)
           pad-stack
           (Call 'raise_error)))]))

(define (externs)
  (seq (Extern 'peek_byte)
       (Extern 'read_byte)
       (Extern 'write_byte)
       (Extern 'raise_error)))

;; [Listof Defn] -> Asm
(define (compile-defines ds)
  (match ds
    ['() (seq)]
    [(cons d ds)
     (seq (compile-define d)
          (compile-defines ds))]))

;; Defn -> Asm
(define (compile-define d)
  (match d
    [(Defn f xs e)
     (seq (Label (symbol->label f))
          (compile-e e (reverse xs))
          (Add rsp (* 8 (length xs))) ; pop args
          (Ret))]))

;; Expr CEnv -> Asm
(define (compile-e e c)
  (match e
    [(Int i)            (compile-value i)]
    [(Bool b)           (compile-value b)]
    [(Char c)           (compile-value c)]
    [(Eof)              (compile-value eof)]
    [(Empty)            (compile-value '())]
    [(Var x)            (compile-variable x c)]
    [(Str s)            (compile-string s)]
    [(Prim0 p)          (compile-prim0 p c)]
    [(Prim1 p e)        (compile-prim1 p e c)]
    [(Prim2 p e1 e2)    (compile-prim2 p e1 e2 c)]
    [(Prim3 p e1 e2 e3) (compile-prim3 p e1 e2 e3 c)]
    [(Values xs)        (compile-values xs c)]
    [(If e1 e2 e3)      (compile-if e1 e2 e3 c)]
    [(Begin e1 e2)      (compile-begin e1 e2 c)]
    [(LetValues xs e e0) 
                        
                           
                          (compile-letValue xs e e0 c)]
    [(Let x e1 e2)        (compile-let x e1 e2 c)]
    [(App f es)           (compile-app f es c)]))

;; Value -> Asm
(define (compile-value v)
  (seq (Mov rax (value->bits v))))

;; Id CEnv -> Asm
(define (compile-variable x c)
  (let ((i (lookup x c)))
    (seq (Mov rax (Offset rsp i)))))

;; String -> Asm
(define (compile-string s)
  (let ((len (string-length s)))
    (if (zero? len)
        (seq (Mov rax type-str))
        (seq (Mov rax len)
             (Mov (Offset rbx 0) rax)
             (compile-string-chars (string->list s) 8)
             (Mov rax rbx)
             (Or rax type-str)
             (Add rbx
                  (+ 8 (* 4 (if (odd? len) (add1 len) len))))))))

;; [Listof Char] Integer -> Asm
(define (compile-string-chars cs i)
  (match cs
    ['() (seq)]
    [(cons c cs)
     (seq (Mov rax (char->integer c))
          (Mov (Offset rbx i) 'eax)
          (compile-string-chars cs (+ 4 i)))]))

;; Op0 CEnv -> Asm
(define (compile-prim0 p c)
  (compile-op0 p))

;; Op1 Expr CEnv -> Asm
(define (compile-prim1 p e c)
(let ((reg-val (gensym 'reg)))
  (seq (compile-e e c)
          (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val)

          (Xor rax type-val)

          (Mov r9 (Offset rax 0))
          (Cmp r9 1)
          (Jne 'raise_error)

          (Mov rax (Offset rax 8))
          (Label reg-val)

       (compile-op1 p))))

;; Op2 Expr Expr CEnv -> Asm
(define (compile-prim2 p e1 e2 c)
 (let ((reg-val1 (gensym 'reg1)) (reg-val2 (gensym 'reg2))) 
 
 (seq (compile-e e1 c)
      
          (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val1)

          (Xor rax type-val)

          (Mov r9 (Offset rax 0))
          (Cmp r9 1)
          (Jne 'raise_error)

          (Mov rax (Offset rax 8))
          (Label reg-val1)

       (Push rax)

       (compile-e e2 (cons #f c))

          (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val2)

          (Xor rax type-val)

          (Mov r9 (Offset rax 0))
          (Cmp r9 1)
          (Jne 'raise_error)

          (Mov rax (Offset rax 8))
          (Label reg-val2)

       (compile-op2 p))))

;; Op3 Expr Expr Expr CEnv -> Asm
(define (compile-prim3 p e1 e2 e3 c)
(let ((reg-val1 (gensym 'reg1)) (reg-val2 (gensym 'reg2))  (reg-val3 (gensym 'reg2))) 
  (seq (compile-e e1 c)
      
      (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val1)

          (Xor rax type-val)

          (Mov r9 (Offset rax 0))
          (Cmp r9 1)
          (Jne 'raise_error)

          (Mov rax (Offset rax 8))
          (Label reg-val1)

       (Push rax)
       (compile-e e2 (cons #f c))

       (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val2)

          (Xor rax type-val)

          (Mov r9 (Offset rax 0))
          (Cmp r9 1)
          (Jne 'raise_error)

          (Mov rax (Offset rax 8))
          (Label reg-val2)

       (Push rax)
       (compile-e e3 (cons #f (cons #f c)))

        (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val3)

          (Xor rax type-val)

          (Mov r9 (Offset rax 0))
          (Cmp r9 1)
          (Jne 'raise_error)

          (Mov rax (Offset rax 8))
          (Label reg-val3)



       (compile-op3 p))))

;; Expr Expr Expr CEnv -> Asm
(define (compile-if e1 e2 e3 c)
  (let ((l1 (gensym 'if))
        (l2 (gensym 'if))
        (reg-val1 (gensym 'reg1))
        (reg-val2 (gensym 'reg2))
        (reg-val3 (gensym 'reg3))
        (re-pack1 (gensym 'repack1))
        (re-pack2 (gensym 'repack2)))
    (seq (compile-e e1 c)

          (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val1)

          (Xor rax type-val)

          (Mov r9 (Offset rax 0))
          (Cmp r9 1)
          (Jne 'raise_error)

          (Mov rax (Offset rax 8))
          (Label reg-val1)



         (Cmp rax (value->bits #f))
         (Je l1)

         (compile-e e2 c)

          (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val2)

          (Xor rax type-val)

          (Mov r9 (Offset rax 0))
          (Cmp r9 1)
          (Jne re-pack1)

          (Mov rax (Offset rax 8))
          (Jmp reg-val2)

          (Label re-pack1)
          (Or rax type-val)

          (Label reg-val2)
          

         (Jmp l2)
         (Label l1)
         (compile-e e3 c)

          (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val3)

          (Xor rax type-val)

          (Mov r9 (Offset rax 0))
          (Cmp r9 1)

          (Jne re-pack2)

          (Mov rax (Offset rax 8))
          (Jmp reg-val3)

          (Label re-pack2)
          (Or rax type-val)

          (Label reg-val3)

         
         (Label l2))))

;;Listof Exp -> Asm

(define (compile-values xs c)
;;push the starting place of the heap (address) in the stack
(seq
(Push rbx)
(Mov 'r9 (length xs))
(Mov (Offset rbx 0) 'r9)
(compile-values-helper xs 8 (cons #f c))
(Add rbx (* 8 (+ 1 (length xs))))
(Pop 'r9)
(Or 'r9 type-val)
(Mov rax 'r9)
))

(define (compile-values-helper xs i c)
(match xs
['() (seq)]
[(cons x xs)   (seq 
                (compile-e x c)
                (Mov (Offset rbx i) rax)
                (compile-values-helper xs (+ i 8) c)
                    )]
))

(define (compile-letValue xs e e0 c)
(let ((reg-val1 (gensym 'regval))
      (end      (gensym 'end)))
        (seq

          (compile-e e c)
          (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val1)

          (Xor rax type-val)
          (Mov r9 (Offset rax 0))

          (Cmp r9 (length xs)) 
          (Jne 'raise_error)


          (helper-letValue xs 8)

                   
          (compile-e e0 (append (reverse xs) c))

          (Add rsp (* 8 (length xs)))
          (Jmp end)


          (Label reg-val1)
          
          (Mov r9 (length xs))

          (Cmp r9 1)
          (Jne 'raise_error)
          (Push rax)
          (compile-e e0 (append  (reverse xs) c))
          (Add rsp 8)

          (Label end)
          
)))

(define (helper-letValue xs i)
(match xs

['()  (seq)]
[(cons x xs)     (seq
                  (Mov r9 (Offset rax i))
                  (Push r9)
                  (helper-letValue xs (+ i 8))
                
                                      )]



))








;; Expr Expr CEnv -> Asm
(define (compile-begin e1 e2 c)
  (seq (compile-e e1 c)
       (compile-e e2 c)))

;; Id Expr Expr CEnv -> Asm
(define (compile-let x e1 e2 c)
  (let ((reg-val1 (gensym 'reg)))
    
    (seq (compile-e e1 c)
      

          (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val1)

          (Xor rax type-val)

          (Mov r9 (Offset rax 0))
          (Cmp r9 1)
          (Jne 'raise_error)
          (Mov rax (Offset rax 8))
          (Label reg-val1)


       (Push rax)
       (compile-e e2 (cons x c))
       (Add rsp 8))))

;; Id [Listof Expr] CEnv -> Asm
;; The return address is placed above the arguments, so callee pops
;; arguments and return address is next frame
(define (compile-app f es c)
  (let ((r (gensym 'ret)))
    (seq (Lea rax r)
         (Push rax)
         (compile-es es (cons #f c))
         (Jmp (symbol->label f))
         (Label r))))

;; [Listof Expr] CEnv -> Asm
(define (compile-es es c)
  (match es
    ['() '()]
    [(cons e es)
     (let ((reg-val1 (gensym 'reg1)))
     
     (seq (compile-e e c)

          (Mov r9 rax)
          (And r9 #b111)
          (Cmp r9 type-val)
          (Jne reg-val1)

          (Xor rax type-val)

          (Mov r9 (Offset rax 0))
          (Cmp r9 1)
          (Jne 'raise_error)
          (Mov rax (Offset rax 8))
          (Label reg-val1)

          (Push rax)
          (compile-es es (cons #f c))))]))

;; Id CEnv -> Integer
(define (lookup x cenv)
  (match cenv
    ['() (error "undefined variable:" x)]
    [(cons y rest)
     (match (eq? x y)
       [#t 0]
       [#f (+ 8 (lookup x rest))])]))

;; Symbol -> Label
;; Produce a symbol that is a valid Nasm label
(define (symbol->label s)
  (string->symbol
   (string-append
    "label_"
    (list->string
     (map (λ (c)
            (if (or (char<=? #\a c #\z)
                    (char<=? #\A c #\Z)
                    (char<=? #\0 c #\9)
                    (memq c '(#\_ #\$ #\# #\@ #\~ #\. #\?)))
                c
                #\_))
         (string->list (symbol->string s))))
    "_"
    (number->string (eq-hash-code s) 16))))
