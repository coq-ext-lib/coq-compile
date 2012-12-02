Require Import CoqCompile.Env.
Require Import CoqCompile.Lambda.
Require Import List.
Require Import String.
Require Import Ascii.
Require Import Bool.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Programming.Show.
Require Import Program.
Require Import Omega.
Require Import Wf.
(* Require Import Wellfounded.Lexicographic_Product. *)
Require Import Relation_Operators.

Set Implicit Arguments.
Set Strict Implicit.

(** A simple, recursive descent parser intended to take the Scheme output
    of the extractor and build a corresponding Lambda.exp.

    A few things are still missing:
    - Scheme comments (e.g., ";;" terminated by end of line.)
    - we probably don't have all of the characters right that can appear
      in identifiers.
    - we probably ought to treat "_" as a variable specially?
    - need comments to explain more in the file.
    - should try to rewrite in a monadic style, but this would require
      a dependent monad.
    - should add error handling support so we can identify what the parse
      error is (or at least at which token it's occurring.)
    - probably should use refine instead of Program and handle more of
      the match stuff myself so that we don't generate > 400 proof
      obligations (ugh).  This would improve the compile time for this
      considerably, at the expense of making the code harder to read/write.

   This is interesting because of the way that I was forced to show
   termination of the parser.  It demonstrates the use of a function
   defined in terms of a well-founded, lexicographic ordering.
*)
Module Parse.
  Import Lambda.

Section monadic.
  Import MonadNotation.
  Local Open Scope monad_scope.

  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Context {MonadExc_m : MonadExc string m}.

  (** Lexing *)
  Inductive token :=
    LPAREN | RPAREN | AT | QUOTE | COMMA | LAMBDA | LAMBDAS | LETREC | LET
  | DEFINE | MATCH | ID : string -> token.

  Section Printing.
    Import ShowNotation.
    Local Open Scope string_scope.
    Local Open Scope show_scope.

    Global Instance Show_token : Show token :=
      fun t =>
        match t with
          | LPAREN => "("
          | RPAREN => ")"
          | AT => "@"
          | QUOTE => "`"
          | COMMA => ","
          | LAMBDA => "lambda"
          | LAMBDAS => "lambdas"
          | LETREC => "letrec"
          | LET => "let"  
          | DEFINE => "define"
          | MATCH => "match"
          | ID s => s ++ " "
        end.

    Global Instance Show_tokens : Show (list token) :=
      fun ts => iter_show (map show ts).

  End Printing.

  Fixpoint list2string (cs:list ascii) : string :=
    match cs with
      | nil => EmptyString
      | c::cs => String c (list2string cs)
    end.

  Fixpoint string2list (s:string) : list ascii :=
    match s with
      | EmptyString => nil
      | String c s' => c::(string2list s')
    end.

  Definition alpha : list ascii :=
    string2list "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".
  Definition numeric : list ascii :=
    string2list "0123456789".
  Definition misc : list ascii := string2list "_~".
  Definition alpha_numeric := numeric ++ alpha.
  Definition id_start := misc ++ alpha.
  Definition id_char := alpha_numeric ++ misc.
  (** linefeed, carriage return, tab, and space *)
  Definition white : list ascii :=
    (ascii_of_nat 9)::(ascii_of_nat 10)::(ascii_of_nat 13)::(ascii_of_nat 32)::nil.

  (** Keyword string to token mapping *)
  Local Open Scope string_scope.
  Definition keywords : list (string * token) :=
    ("lambda",LAMBDA)::
    ("lambdas",LAMBDAS)::
    ("letrec",LETREC)::
    ("let",LET)::
    ("define",DEFINE)::
    ("match",MATCH)::
    nil.

  Fixpoint lookup {A} (x:string) (xs:list (string * A)) : option A :=
    match xs with
      | nil => None
      | (y,c)::t => if eq_dec y x then Some c else lookup x t
    end.

  Definition id_to_token (s:string) : token :=
    match lookup s keywords with
      | None => ID s
      | Some x => x
    end.

  Fixpoint member(c:ascii)(cs:list ascii) : bool :=
    match cs with
      | nil => false
      | c'::cs => if eq_dec c c' then true else member c cs
    end.

  (** Pull off characters from the string to form an identifier.  [cs] is
      the list of characters accumulated (in reverse order). *)
  Fixpoint token_id (s:string) (cs:list ascii) : token * string :=
    match s with
      | EmptyString => (id_to_token (list2string (rev cs)), EmptyString)
      | String c s' =>
        if member c id_char then token_id s' (c::cs) else
          (id_to_token (list2string (rev cs)), String c s')
    end.

  (** Needed to show termination for [tokenize] below. *)
  Lemma token_id_lt : forall s cs, length (snd (token_id s cs)) <= length s.
  Proof.
    induction s. simpl. intro ; auto with arith. intros.
    unfold token_id. fold token_id. destruct (member a id_char).
    specialize (IHs (a::cs)). assert (length (String a s) = S (length s)). auto.
    rewrite H. omega. simpl. auto with arith.
  Qed.

  Section TOKENIZE.
    Import Ascii.
    Local Open Scope char_scope.

    (** Converts a string into a list of tokens.  The [measure] annotation
        says that we are defining this not by structural induction, but rather
        using the well-founded order [lt] (less-than) on [nat] relative to
        the length of the input string.  That is, we must argue that the string
        is getting smaller each time around the loop. *)
    Program Fixpoint tokenize (s:string) (ts : list token) {measure (length s)} :
      option (list token) :=
      match s with
        | EmptyString => Some (rev ts)
        | String c s' =>
          if member c white then tokenize s' ts
          else if eq_dec c "(" then tokenize s' (LPAREN::ts)
          else if eq_dec c ")" then tokenize s' (RPAREN::ts)
          else if eq_dec c "@" then tokenize s' (AT::ts)
          else if eq_dec c "`" then tokenize s' (QUOTE::ts)
          else if eq_dec c "," then tokenize s' (COMMA::ts)
          else if member c id_start then
            match token_id s' (c::nil) with
              | (t,s'') => tokenize s'' (t::ts)
            end
          else None
      end.
    Next Obligation.
      clear tokenize. generalize (token_id_lt s' [c]). rewrite <- Heq_anonymous. simpl.
      intros. omega.
    Defined.
  End TOKENIZE.

  Section parse_list.
    Variable A : Type.
    Variable p : list token -> m (A * list token).

    Fixpoint parse_list (ts:list token) (fuel:nat) : m ((list A) * (list token)) :=
      match fuel with
        | O => raise "Ran out of fuel during parse_exp'list"
        | S fuel =>
          res <- p ts ;;
          let '(e,ts2) := res in
          res <- parse_list ts2 fuel ;;
          let '(es,ts3) := res in
          ret (e::es,ts3)
      end.
  End parse_list.

  Fixpoint parse_exp' (ts:list token) (fuel:nat) : m (exp * (list token)) :=
    match fuel with
      | O => raise "Ran out of fuel during parse_exp'"
      | S fuel =>
        match ts with
        (* EXP -> <ID> *)
          | (ID x)::ts2 => ret (Var_e (Env.wrapVar x), ts2)
        (* EXP -> (lambda (<ID>) <EXP>) *)
          | LPAREN::LAMBDA::LPAREN::(ID x)::RPAREN::ts2 =>
            res <- parse_exp' ts2 fuel ;;
            match res with
              | (e,RPAREN::ts3) => ret (Lam_e (Env.wrapVar x) e,ts3)
              | _ => raise "Error parsing lambda, expecting expression"
            end
          (* EXP -> (lambdas (<ARGLIST>) <EXP>) *)
          | LPAREN::LAMBDAS::LPAREN::ts2 =>
            res <- parse_arglist ts2 fuel ;;
            match res with
              | (xs,RPAREN::ts3) =>
                res <- parse_exp' ts3 fuel ;;
                match res with
                  | (e,RPAREN::ts4) =>
                    ret (fold_right Lam_e e xs,ts4)
                  | _ => raise "Error parsing lambda, expecting expression"
                end
              | _ => raise "Error parsing lambda, expecting arguments"
            end
          (* EXP -> `(<ID> <CONARGLIST>) *)
          | QUOTE::LPAREN::(ID c)::ts2 =>
            res <- parse_conarglist ts2 fuel ;;
            match res with
              | (es,RPAREN::ts3) =>
                ret (Con_e c es,ts3)
              | _ => raise "Error parsing constructor"
            end
          (* EXP -> (@ <EXPLIST>) *)
          | LPAREN::AT::ts2 =>
            res <- parse_exp' ts2 fuel ;;
            match res with
              | (e1,ts3) =>
                res <- parse_list (fun x => parse_exp' x fuel) ts3 (S fuel) ;;
                match res with
                  | (es,RPAREN::ts4) =>
                    ret (fold_left App_e es e1,ts4)
                  | _ => raise "Error parsing unquote, expecting expression list"
                end
            end
          (* EXP -> (match <EXP> <ARMLIST>) *)
          | LPAREN::MATCH::ts1 =>
            res <- parse_exp' ts1 fuel ;;
            match res with
              | (e,ts2) =>
                res <- parse_armlist ts2 fuel ;;
                match res with
                  | (arms,RPAREN::ts3) =>
                    ret (Match_e e arms,ts3)
                  | _ => raise "Error parsing match, expecting arm list"
                end
            end
          (* EXP -> (letrec (<DECLLIST>) <EXP>) *)
          | LPAREN::LETREC::LPAREN::ts1 =>
            res <- parse_decllist ts1 fuel ;;
            match res with
              | (ds,RPAREN::ts2) =>
                res <- parse_exp' ts2 fuel ;;
                match res with
                  | (e,RPAREN::ts3) =>
                    ret (Letrec_e ds e,ts3)
                  | _ => raise "Error parsing letrec, expecting expression"
                end
              | _ => raise "Error parsing letrec, expecting declaration list"
            end
          (* EXP -> (let (<DECL>) <EXP>) *)
          | LPAREN::LET::LPAREN::ts1 =>
            res <- parse_decl ts1 fuel ;;
            match res with
              | ((v,d),RPAREN::ts2) =>
                res <- parse_exp' ts2 fuel ;;
                match res with
                  | (e,RPAREN::ts3) =>
                    ret (Let_e v d e,ts3)
                  | _ => raise "Error parsing let, expecting expression"
                end
              | _ => raise "Error parsing let, expecting declaration"
            end
          (* EXP -> (<EXP> <EXP>) *)
          | LPAREN::ts2 =>
            res <- parse_exp' ts2 fuel ;;
            match res with
              | (e1,ts3) =>
                res <- parse_exp' ts3 fuel ;;
                match res with
                  | (e2,RPAREN::ts4) =>
                    ret (App_e e1 e2,ts4)
                  | _ => raise "Error parsing application, expecting expression"
                end
            end
          | t::ts => raise ("Error parsing expression, unexpected token " ++ (to_string t) ++ " while trying to parse " ++ to_string (t::ts))%string
          | nil => raise "Error parsing expression, unexpected EOF"
        end
    end

  with parse_conarglist (ts:list token) (fuel:nat) : m ((list exp) * (list token)) :=
    match fuel with
      | O => raise "Ran out of fuel during parse_conarglist"
      | S fuel =>
        match ts with
          | COMMA::ts1 =>
            res <- parse_exp' ts1 fuel ;;
            let '(e,ts2) := res in
            res <- parse_conarglist ts2 fuel ;;
            let '(es,ts3) := res in
            ret (e::es,ts3)
          | _ => ret (nil,ts)
        end
    end

  with parse_arglist (ts:list token) (fuel:nat) : m ((list var) * (list token)) :=
    match fuel with
      | O => raise "Ran out of fuel during parse_arglist"
      | S fuel =>
      (* ARGLIST -> <ID> <ARGLIST> | epsilon *)
        match ts with
          | (ID x)::ts2 =>
            res <- parse_arglist ts2 fuel ;;
            let '(xs,ts3) := res in
            ret (Env.wrapVar x::xs,ts3)
          | _ => ret (nil,ts)
        end
    end

  with parse_armlist (ts:list token) (fuel:nat) : m ((list (pattern*exp)) * (list token)) :=
    match fuel with
      | O => raise "Ran out of fuel during parse_armlist"
      | S fuel =>
      (* ARMLIST -> ((<ID> <ARGLIST>) <EXP>) ARMLIST | epsilon *)
        match ts with
          | LPAREN::LPAREN::(ID c)::ts1 =>
            res <- parse_arglist ts1 fuel ;;
            match res with
              | (xs,RPAREN::ts2) =>
                res <- parse_exp' ts2 fuel ;;
                match res with
                  | (e,RPAREN::ts3) =>
                    res <- parse_armlist ts3 fuel ;;
                    let '(arms,ts4) := res in
                    ret ((Con_p c xs,e)::arms,ts4)
                  | _ => raise "Error parsing arm list"
                end
              | _ => raise "Error parsing arm list"
            end
          | _ => ret (nil,ts)
        end
    end

  with parse_decl (ts:list token) (fuel:nat) : m ((var * exp) * (list token)) :=
    match fuel with
      | O => raise "Ran out of fuel during parse_decl"
      | S fuel =>
        match ts with
          | LPAREN::(ID v)::ts1 =>
            res <- parse_exp' ts1 fuel ;;
            match res with
              | (e,RPAREN::ts2) =>
                ret ((Env.wrapVar v,e),ts2)
              | _ => raise "Error parsing declaration, expecting expression"
            end
          | _ => raise "Error parsing declaration, expecting id"
        end 
    end

  with parse_decllist (ts:list token) (fuel:nat) : m ((list (var*(var*exp))) * (list token)) :=
    match fuel with
      | O => raise "Ran out of fuel during parse_decllist"
      | S fuel =>
        match ts with
          | LPAREN::(ID f)::ts1 =>
            res <- parse_exp' ts1 fuel ;;
            match res with
              | (Lam_e x e,RPAREN::ts2) =>
                res <- parse_decllist ts2 fuel ;;
                let '(ds,ts3) := res in
                ret ((Env.wrapVar f,(x,e))::ds,ts3)
              | _ => raise "Error parsing declaration list, expecting lambda term"
            end
          | _ => ret (nil,ts)
        end
    end.


  (** Parsing *)
  Fixpoint parse (ts:list token) (fuel:nat) : m (list (var * exp)) :=
    match fuel with
      | O => raise "Ran out of fuel during parse"
      | S fuel =>
        match ts with
          | nil => ret nil
          | LPAREN::DEFINE::(ID x)::ts1 =>
            res <- parse_exp' ts1 fuel ;;
            match res with
              | (e,RPAREN::ts2) =>
                es <- parse ts2 fuel ;;
                ret ((Env.wrapVar x,e)::es)
              | _ => raise "Parse error while parsing define"
            end
          | _ => raise "Parse error while parsing definitions"
        end
    end.

End monadic.

  (** A parser for expresions *)
  Definition parse_exp (s:string) : string + (exp * list token) :=
    match tokenize s nil with
      | None => inl "Parse error: tokenizer failed"%string
      | Some ts => parse_exp' ts (List.length ts) 
    end.

  (** Some test cases -- should turn these into real unit tests. *)
(*
  Eval compute in parse_exp "x".
  Eval compute in parse_exp "(@ f x y)".
  Eval compute in parse_exp "(f x)".
  Eval compute in parse_exp "`(Cons ,a ,b)".
  Eval compute in parse_exp "`(Z)".
  Eval compute in parse_exp "(lambda (x) x)".
  Eval vm_compute in parse_exp "(lambdas (x1 x2 x3) (@x3 x2 x1))".
  Eval vm_compute in parse_exp "(match x ((Cons hd tl) hd) ((Nil) x))".
  Eval vm_compute in parse_exp "(letrec ((f (lambda (x) (f x)))) f)".
*)

  (** Collapse a list of top-level declarations into a big sequence of "lets".
      However, we simply assume that any function defined at the top-level is
      recursive and so use a "letrec" for lambdas.  We could try to do something
      smarter, like see if the function really is recursive, but that's something
      we can leave to the optimizer. *)
  Fixpoint collapse_decls (ds:list (var*exp)) (fs:env_t (var * exp)) (e:exp) : exp :=
    match ds with
      | nil => match rev fs with 
                 | nil => e
                 | fs' => Letrec_e fs' e
               end
      | (f,(Lam_e x e'))::rest => collapse_decls rest ((f,(x,e'))::fs) e
      | (x,e')::rest => 
        match rev fs with 
          | nil => Let_e x e' (collapse_decls rest nil e)
          | fs' => Letrec_e fs' (Let_e x e' (collapse_decls rest nil e))
        end
    end.

  Fixpoint lastDecl (ds : list (var * exp)) : option var :=
    match ds with
      | nil => None
      | (v,_) :: nil => Some v
      | _ :: ds => lastDecl ds
    end.
    
  (** Parse a set of top-level declarations and return a bit "let", binding
      those declarations, terminated by a call to "main tt".  Of course, this
      is only meaningful if one of the declarations binds a function that takes
      unit as an argument... *)
  Definition parse_topdecls (s:string) : string + exp :=
    match tokenize s nil with
      | None => inl "Parse error: tokenizer failed"%string
      | Some ts => match parse ts (List.length ts) with
                     | inl e => inl e
                     | inr ds =>
                       let body := 
                         match lastDecl ds with
                           | None => Con_e "Tt"%string nil
                           | Some v => Var_e v
                           end
                       in
                       inr (collapse_decls ds nil body)
                   end
    end.

  (** A relatively big test case that I got by extracting some real code using
      [Extraction Language Scheme].  We probably want to add some support for
      skipping the comments at the top of a file, as well as the
      "(load ...)" so that we can just pipe the output of the extractor directly
      into the parser.  But at least for now, this will be useful for building
      modestly sized Lambda expressions. *)
(*
  Eval vm_compute in parse_topdecls
"(define negb (lambda (b)
  (match b
     ((True) `(False))
     ((False) `(True)))))

(define fst (lambda (p0)
  (match p0
     ((Pair x y) x))))

(define snd (lambda (p0)
  (match p0
     ((Pair x y) y))))

(define app (lambdas (l m)
  (match l
     ((Nil) m)
     ((Cons a l1) `(Cons ,a ,(@ app l1 m))))))

(define compareSpec2Type (lambda (c)
  (match c
     ((Eq) `(CompEqT))
     ((Lt) `(CompLtT))
     ((Gt) `(CompGtT)))))

(define compSpec2Type (lambdas (x y c) (compareSpec2Type c)))

(define plus (lambdas (n m)
  (match n
     ((O) m)
     ((S p0) `(S ,(@ plus p0 m))))))

(define mult (lambdas (n m)
  (match n
     ((O) `(O))
     ((S p0) (@ plus m (@ mult p0 m))))))

(define minus (lambdas (n m)
  (match n
     ((O) n)
     ((S k)
       (match m
          ((O) n)
          ((S l) (@ minus k l)))))))

(define nat_iter (lambdas (n f x)
  (match n
     ((O) x)
     ((S n~) (f (@ nat_iter n~ f x))))))
".
*)
End Parse.

