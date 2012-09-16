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
  (** The parser below has a number of different "states" which represent
      functions that I wish I could break out into a set of mutually-
      recursive functions.  Alas, the [Program Fixpoint] construct doesn't
      support mutual recursion.  So the states represent which function 
      I'm really meaning to be in. *)
  Inductive state : Type := 
  | TOPDECL | EXP | EXPLIST | CONARGLIST | ARGLIST | ARMLIST | DECLLIST.

  Import List.  (* to avoid notation conflicts with String. *)

  (** Each state has a distinct answer type.  Some of these don't really need to
      be options.   For many of the cases, we need to also know that we've 
      consumed the input stream of tokens, or at least that the input is no bigger. 
      So even though I wish I could break parse into separate functions, it's
      at least nice that the return type for the different states can be broken
      out this way. *)
  Definition result(ts:list token)(s:state) : Type := 
    match s with 
      | TOPDECL => option (list (var * exp))
      | EXP => option {p : exp * (list token) & length (snd p) < length ts}
      | EXPLIST => option {p: (list exp) * (list token) & length (snd p) <= length ts}
      | ARGLIST => option {p: (list var) * (list token) & length (snd p) <= length ts}
      | CONARGLIST => option {p: (list exp)*(list token) & length (snd p) <= length ts}
      | ARMLIST => option {p:(list (pattern*exp))*(list token) & 
                                length (snd p) <= length ts}
      | DECLLIST => option {p:(list (var*(var*exp)))*(list token) &
                            length (snd p) <= length ts}
    end.

  (** We need to define an order on states.  This is because I want to be able
      to have some states invoke the parser on other states without consuming
      any input.  So to ensure that we don't loop infinitely, we just need that
      the [EXP] state is "less than" the other states that invoke it. *)
  Definition state2nat (s:state) : nat := 
    match s with 
      | EXP => 0
      | EXPLIST => 1
      | CONARGLIST => 2
      | ARGLIST => 3
      | ARMLIST => 4
      | DECLLIST => 5
      | TOPDECL => 6
    end.

  (** Our well-founded order for the parser will be the lexicographic order
      on pairs of a token list and a state.  So each time around the loop,
      either the token list gets shorter, or else the state goes down 
      according to the order above. *)
  Definition state_list_lt := 
    @lexprod (list token) (fun _ => state)
    (fun ts1 ts2 => length ts1 < length ts2)
    (fun ts s1 s2 => state2nat s1 < state2nat s2).

  (** The [measure] annotation says that we are using the [state_list_lt] relation
      on pairs of lists of tokens and a state to ensure termination.  One of the
      proof obligations that is generated is showing that [state_list_lt] is 
      a well-founded relation (i.e., has no infinite descending chain).  The
      other proof obligations arise from needing to prove that we are going down
      in the [state_list_lt] order each time we go through the loop, or else
      arise from simple type equations/ordering issues due to the use of [Program]. 
      All of this is just to convince Coq that the parser terminates!
  *)
  Program Fixpoint parse (ts:list token) (s:state) 
    {measure (existT _ ts s) (state_list_lt)} : result ts s :=
    match s with
      | TOPDECL => 
        (** TOPDECL -> (define x <EXP>) <TOPDECL> | epsilon *)
        match ts with
          | nil => Some nil
          | LPAREN::DEFINE::(ID x)::ts1 => 
            match parse ts1 EXP with 
              | Some (existT (e,RPAREN::ts2) H2) => 
                match parse ts2 TOPDECL with
                  | Some es => Some ((x,e)::es) 
                  | _ => None
                end
              | _ => None
            end
          | _ => None
        end
      | EXP => 
        match ts with 
          (* EXP -> <ID> *)
          | (ID x)::ts2 => Some (existT _ (Var_e x, ts2) _)
          (* EXP -> (lambda (<ID>) <EXP>) *)
          | LPAREN::LAMBDA::LPAREN::(ID x)::RPAREN::ts2 => 
            match parse ts2 EXP with 
              | Some (existT (e,RPAREN::ts3) H3) => 
                Some (existT _ (Lam_e x e,ts3) _)
              | _ => None
            end
          (* EXP -> (lambdas (<ARGLIST>) <EXP>) *)
          | LPAREN::LAMBDAS::LPAREN::ts2 => 
            match parse ts2 ARGLIST with 
              | Some (existT (xs,RPAREN::ts3) H3) => 
                match parse ts3 EXP with 
                  | Some (existT (e,RPAREN::ts4) H4) => 
                    Some (existT _ (fold_right Lam_e e xs,ts4) _)
                  | _ => None
                end
              | _ => None
            end
          (* EXP -> `(<ID> <CONARGLIST>) *)
          | QUOTE::LPAREN::(ID c)::ts2 => 
            match parse ts2 CONARGLIST with 
              | Some (existT (es,RPAREN::ts3) H3) => 
                Some (existT _ (Con_e c es,ts3) _)
              | _ => None
            end
          (* EXP -> (@ <EXPLIST>) *)
          | LPAREN::AT::ts2 => 
            match parse ts2 EXP with 
              | Some (existT (e1,ts3) H3) => 
                match parse ts3 EXPLIST with 
                  | Some (existT (es,RPAREN::ts4) H4) => 
                    Some (existT _ (fold_left App_e es e1,ts4) _)
                  | _ => None
                end
              | _ => None
            end
          (* EXP -> (match <EXP> <ARMLIST>) *)
          | LPAREN::MATCH::ts1 => 
            match parse ts1 EXP with 
              | Some (existT (e,ts2) H2) => 
                match parse ts2 ARMLIST with 
                  | Some (existT (arms,RPAREN::ts3) H3) => 
                    Some (existT _ (Match_e e arms,ts3) _)
                  | _ => None
                end
              | _ => None
            end
          (* EXP -> (letrec (<DECLLIST>) <EXP>) *)
          | LPAREN::LETREC::LPAREN::ts1 => 
            match parse ts1 DECLLIST with
              | Some (existT (ds,RPAREN::ts2) H2) => 
                match parse ts2 EXP with 
                  | Some (existT (e,RPAREN::ts3) H3) => 
                    Some (existT _ (Letrec_e ds e,ts3) _)
                  | _ => None
                end
              | _ => None
            end
          (* EXP -> (<EXP> <EXP>) *)
          | LPAREN::ts2 => 
            match parse ts2 EXP with
              | Some (existT (e1,ts3) H3) => 
                match parse ts3 EXP with 
                  | Some (existT (e2,RPAREN::ts4) H4) => 
                    Some (existT _ (App_e e1 e2,ts4) _)
                  | _ => None
                end
              | _ => None
            end
          | _ => None
        end
      (* EXPLIST -> <EXP> <EXPLIST> | epsilon *)
      | EXPLIST => 
        match parse ts EXP with 
          | Some (existT (e,ts2) H2) => 
            match parse ts2 EXPLIST with 
              | Some (existT (es,ts3) H3) => Some (existT _ (e::es,ts3) _)
              | None => None
            end
          | None => Some (existT _ (nil,ts) _)
        end
      (* CONARGLIST -> ,<EXP> <CONARGLIST> | epsilon *)
      | CONARGLIST => 
        match ts with 
          | COMMA::ts1 => 
            match parse ts1 EXP with 
              | Some (existT (e,ts2) H2) =>
                match parse ts2 CONARGLIST with 
                  | Some (existT (es,ts3) H3) => Some (existT _ (e::es,ts3) _)
                  | None => None
                end
              | None => None
            end
          | _ => Some (existT _ (nil,ts) _)
        end
      (* ARGLIST -> <ID> <ARGLIST> | epsilon *)
      | ARGLIST => 
        match ts with 
          | (ID x)::ts2 => 
            match parse ts2 ARGLIST with 
              | Some (existT (xs,ts3) H3) => 
                Some (existT _ (x::xs,ts3) _)
              | _ => None
            end
          | _ => Some (existT _ (nil,ts) _)
        end
      (* ARMLIST -> ((<ID> <ARGLIST>) <EXP>) ARMLIST | epsilon *)
      | ARMLIST => 
        match ts with 
          | LPAREN::LPAREN::(ID c)::ts1 => 
            match parse ts1 ARGLIST with 
              | Some (existT (xs,RPAREN::ts2) H2) => 
                match parse ts2 EXP with 
                  | Some (existT (e,RPAREN::ts3) H3) =>
                    match parse ts3 ARMLIST with 
                      | Some (existT (arms,ts4) H4) => 
                        Some (existT _ ((Con_p c xs,e)::arms,ts4) _)
                      | _ => None
                    end
                  | _ => None
                end
              | _ => None
            end
          | _ => Some (existT _ (nil,ts) _)
        end 
      | DECLLIST => 
        match ts with 
          | LPAREN::(ID f)::ts1 => 
            match parse ts1 EXP with 
              | Some (existT (Lam_e x e,RPAREN::ts2) H2) => 
                match parse ts2 DECLLIST with 
                  | Some (existT (ds,ts3) H3) => 
                    Some (existT _ ((f,(x,e))::ds,ts3) _)
                  | _ => None
                end
              | _ => None
            end
          | _ => Some (existT _ (nil,ts) _)
        end
    end.
  (* Tactic for knocking off all of the obligations except the well-foundedness
     of [state_list_lt]. *)
  Solve Obligations using
    simpl ; intros ; subst ; simpl in * ; auto ;
    match goal with 
      | [ |- state_list_lt _ _ ] => 
        eapply left_lex ; simpl ; auto with arith ; omega ; fail
      | [ |- state_list_lt _ _] => 
        eapply right_lex ; simpl ; auto with arith ; omega
      | _ => intuition ; congruence
    end.
   Next Obligation.
     (* This is conveniently proved using lemmas from the libraries.  To prove
        that [state_list_lt] is well-founded, we use the [wf_lexprod] lemma which
        basically makes us show that the two relations we used on the pairs are
        well-founded.  In turn, these reduce to showing that a relation 
        [fun x y -> (f x) < (f y)] is well founded for some [f:A->nat], which
        is conveniently provided by the [well_founded_ltof] lemma. *)
     apply measure_wf. unfold state_list_lt. apply wf_lexprod.
     apply (well_founded_ltof (list token) (fun x => length x)). intros.
     apply (well_founded_ltof state state2nat).
   Defined.

  (** A parser for expresions *)
  Definition parse_exp (s:string) : option (exp * list token) := 
    match tokenize s nil with 
      | None => None
      | Some ts => match parse ts EXP with 
                     | None => None
                     | Some (existT (e,ts) _) => Some (e,ts)
                   end
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
  Fixpoint collapse_decls (ds:list (var*exp)) (e:exp) : exp :=
    match ds with 
      | nil => e
      | (f,(Lam_e x e'))::rest => Letrec_e ((f,(x,e'))::nil) (collapse_decls rest e)
      | (x,e')::rest => Let_e x e' (collapse_decls rest e)
    end.

  (** Parse a set of top-level declarations and return a bit "let", binding
      those declarations, terminated by a call to "main tt".  Of course, this
      is only meaningful if one of the declarations binds a function that takes
      unit as an argument... *)
  Definition parse_topdecls (s:string) : option exp := 
    match tokenize s nil with 
      | None => None
      | Some ts => match parse ts TOPDECL with
                     | None => None
                     | Some ds => 
                       Some (collapse_decls ds (App_e (Var_e "main") (Con_e "Tt" nil)))
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
  