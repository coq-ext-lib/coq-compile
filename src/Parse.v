Require Import Lambda.
Require Import List.
Require Import String.
Require Import Ascii.
Require Import Bool.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Decidables.Decidable.
Require Import Program.
Require Import Omega.
Require Import Wf.
Require Import Wellfounded.Lexicographic_Product.
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
  (** Lexing *)
  Inductive token :=
    LPAREN | RPAREN | AT | QUOTE | COMMA | LAMBDA | LAMBDAS | LETREC
  | DEFINE | MATCH | ID : string -> token.

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

  (** Parsing *)
  Fixpoint parse (ts:list token) (fuel:nat) : option (list (var * exp)) :=
    match fuel with
      | O => None
      | S fuel =>
        match ts with
          | nil => Some nil
          | LPAREN::DEFINE::(ID x)::ts1 =>
            match parse_exp' ts1 fuel with
              | Some (e,RPAREN::ts2) =>
                match parse ts2 fuel with
                  | Some es => Some ((x,e)::es)
                  | _ => None
                end
              | _ => None
            end
          | _ => None
        end
    end
  with parse_exp' (ts:list token) (fuel:nat) : option (exp * (list token)) :=
    match fuel with
      | O => None
      | S fuel =>
        match ts with
        (* EXP -> <ID> *)
          | (ID x)::ts2 => Some (Var_e x, ts2)
        (* EXP -> (lambda (<ID>) <EXP>) *)
          | LPAREN::LAMBDA::LPAREN::(ID x)::RPAREN::ts2 =>
            match parse_exp' ts2 fuel with
              | Some (e,RPAREN::ts3) => Some (Lam_e x e,ts3)
              | _ => None
            end
          (* EXP -> (lambdas (<ARGLIST>) <EXP>) *)
          | LPAREN::LAMBDAS::LPAREN::ts2 =>
            match parse_arglist ts2 fuel with
              | Some (xs,RPAREN::ts3) =>
                match parse_exp' ts3 fuel with
                  | Some (e,RPAREN::ts4) =>
                    Some (fold_right Lam_e e xs,ts4)
                  | _ => None
                end
              | _ => None
            end
          (* EXP -> `(<ID> <CONARGLIST>) *)
          | QUOTE::LPAREN::(ID c)::ts2 =>
            match parse_conarglist ts2 fuel with
              | Some (es,RPAREN::ts3) =>
                Some (Con_e c es,ts3)
              | _ => None
            end
          (* EXP -> (@ <EXPLIST>) *)
          | LPAREN::AT::ts2 =>
            match parse_exp' ts2 fuel with
              | Some (e1,ts3) =>
                match parse_exp'list ts3 fuel with
                  | Some (es,RPAREN::ts4) =>
                    Some (fold_left App_e es e1,ts4)
                  | _ => None
                end
              | _ => None
            end
          (* EXP -> (match <EXP> <ARMLIST>) *)
          | LPAREN::MATCH::ts1 =>
            match parse_exp' ts1 fuel with
              | Some (e,ts2) =>
                match parse_armlist ts2 fuel with
                  | Some (arms,RPAREN::ts3) =>
                    Some (Match_e e arms,ts3)
                  | _ => None
                end
              | _ => None
            end
          (* EXP -> (letrec (<DECLLIST>) <EXP>) *)
          | LPAREN::LETREC::LPAREN::ts1 =>
            match parse_decllist ts1 fuel with
              | Some (ds,RPAREN::ts2)=>
                match parse_exp' ts2 fuel with
                  | Some (e,RPAREN::ts3) =>
                    Some (Letrec_e ds e,ts3)
                  | _ => None
                end
              | _ => None
            end
          (* EXP -> (<EXP> <EXP>) *)
          | LPAREN::ts2 =>
            match parse_exp' ts2 fuel with
              | Some (e1,ts3) =>
                match parse_exp' ts3 fuel with
                  | Some (e2,RPAREN::ts4) =>
                    Some (App_e e1 e2,ts4)
                  | _ => None
                end
              | _ => None
            end
          | _ => None
        end
    end
  with parse_exp'list (ts:list token) (fuel:nat) : option ((list exp) * (list token)) :=
    match fuel with
      | O => None
      | S fuel =>
        match parse_exp' ts fuel with
          | Some (e,ts2) =>
            match parse_exp'list ts2 fuel with
              | Some (es,ts3) => Some (e::es,ts3)
              | None => None
            end
          | None => Some (nil,ts)
        end
    end
  with parse_conarglist (ts:list token) (fuel:nat) : option ((list exp) * (list token)) :=
    match fuel with
      | O => None
      | S fuel =>
        match ts with
          | COMMA::ts1 =>
            match parse_exp' ts1 fuel with
              | Some (e,ts2) =>
                match parse_conarglist ts2 fuel with
                  | Some (es,ts3) => Some (e::es,ts3)
                  | None => None
                end
              | None => None
            end
          | _ => Some (nil,ts)
        end
    end
  with parse_arglist (ts:list token) (fuel:nat) : option ((list var) * (list token)) :=
    match fuel with
      | O => None
      | S fuel =>
      (* ARGLIST -> <ID> <ARGLIST> | epsilon *)
        match ts with
          | (ID x)::ts2 =>
            match parse_arglist ts2 fuel with
              | Some (xs,ts3) =>
                Some (x::xs,ts3)
              | _ => None
            end
          | _ => Some (nil,ts)
        end
    end
  with parse_armlist (ts:list token) (fuel:nat) : option ((list (pattern*exp)) * (list token)) :=
    match fuel with
      | O => None
      | S fuel =>
      (* ARMLIST -> ((<ID> <ARGLIST>) <EXP>) ARMLIST | epsilon *)
        match ts with
          | LPAREN::LPAREN::(ID c)::ts1 =>
            match parse_arglist ts1 fuel with
              | Some (xs,RPAREN::ts2) =>
                match parse_exp' ts2 fuel with
                  | Some (e,RPAREN::ts3) =>
                    match parse_armlist ts3 fuel with
                      | Some (arms,ts4) =>
                        Some ((Con_p c xs,e)::arms,ts4)
                      | _ => None
                    end
                  | _ => None
                end
              | _ => None
            end
          | _ => Some (nil,ts)
        end
    end
  with parse_decllist (ts:list token) (fuel:nat) : option ((list (var*(var*exp))) * (list token)) :=
    match fuel with
      | O => None
      | S fuel =>
        match ts with
          | LPAREN::(ID f)::ts1 =>
            match parse_exp' ts1 fuel with
              | Some (Lam_e x e,RPAREN::ts2) =>
                match parse_decllist ts2 fuel with
                  | Some (ds,ts3) =>
                    Some ((f,(x,e))::ds,ts3)
                  | _ => None
                end
              | _ => None
            end
          | _ => Some (nil,ts)
        end
    end.

  (** A parser for expresions *)
  Definition parse_exp (s:string) : option (exp * list token) :=
    match tokenize s nil with
      | None => None
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

  (** Parse a set of top-level declarations and return a bit "let", binding
      those declarations, terminated by a call to "main tt".  Of course, this
      is only meaningful if one of the declarations binds a function that takes
      unit as an argument... *)
  Definition parse_topdecls (s:string) : option exp :=
    match tokenize s nil with
      | None => None
      | Some ts => match parse ts (List.length ts) with
                     | None => None
                     | Some ds =>
                       Some (collapse_decls ds nil (App_e (Var_e "main") (Con_e "Tt" nil)))
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

