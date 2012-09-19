Require Import List.
Require Import Ascii.
Require Import ExtLib.Data.HList ExtLib.Data.Strings.
Require Import ExtLib.Rec.GenRec.
Require Import ExtLib.Decidables.Decidable.
Require Import ExtLib.Monad.Monad.

Set Implicit Arguments.
Set Strict Implicit.

Section charset.
  Variable Tok : Type.
  Definition stream : Type := list Tok.

  Inductive Parse (init : stream) (t : Type) : Type :=
  | Fail    : Parse init t
  | Epsilon : t -> Parse init t
  | Consume : t -> forall rest : stream,
    length rest < length init -> Parse init t.

  Arguments Fail {_} {_}.
  Arguments Epsilon {_} {_} (t).
  Arguments Consume {_} {_} (t) (rest) (pf).

  Variable m : Type -> Type.
  Context {Mon_m : Monad m}.

  Definition ParserT (T : Type) : Type :=
    forall s : stream, m (Parse s T).

  Global Instance Monad_ParserT : Monad ParserT :=
  { ret  := fun _ v => fun _ => ret (Epsilon v)
  ; bind := fun _ c1 _ c2 =>
    fun s =>
      bind (c1 s) (fun r =>
      match r with
        | Fail => ret Fail
        | Epsilon v => c2 v s
        | Consume v rest pf =>
          bind (c2 v rest) (fun r =>
          match r with
            | Fail => ret Fail
            | Epsilon u => ret (Consume u rest pf)
            | Consume u rest pf' =>
              let pf := RelationClasses.transitivity pf' pf in
              ret (Consume u rest pf)
          end)
      end) }.

  Global Instance MonadT_ParserT : MonadT ParserT m :=
  { lift := fun _ c => fun s => bind c (fun x => ret (Epsilon x)) }.

  Global Instance Zero_ParserT : Zero ParserT :=
  { zero := fun _ _ => ret Fail }.

  Definition runParserT {T} (p : ParserT T) (s : stream) : m (option T) :=
    bind (p s) (fun r =>
      match r with
        | Fail => ret None
        | Epsilon v => ret (Some v)
        | Consume v _ _ => ret (Some v)
      end).

  Definition fail {T : Type} : ParserT T := zero.

  Definition map {T U} (f : T -> m U) (p : ParserT T) : ParserT U :=
    bind p (fun x => lift (f x)).

  Definition satisfies (f : Tok -> bool) : ParserT Tok :=
    fun s =>
      match s with
        | nil => ret Fail
        | a' :: s =>
          if f a' then ret (Consume a' s (le_n (length (a' :: s))))
          else ret Fail
      end.

  Definition epsilon {T : Type} (v : T) : ParserT T :=
    fun _ => ret (Epsilon v).

  Definition seq {T} (p1 : ParserT T) {U} (p2 : ParserT U) : ParserT (T * U) :=
    bind p1 (fun u =>
      bind p2 (fun v => ret (u, v))).

  Definition alt {T} (p1 p2 : ParserT T) : ParserT T :=
    fun s =>
      bind (p1 s) (fun r =>
        match r with
          | Fail => p2 s
          | x => ret x
        end).

  Definition EParserT (ls : list Type) (T : Type) :=
    (forall a, member a ls -> ParserT a) -> ParserT T.

  Definition star {T} (p : ParserT T) : ParserT (list T) :=
    Fix (@wf_R_list_len _)
        (fun s => m (Parse s (list T)))
        (fun x rec =>
          bind (p x) (fun r =>
            match r with
              | Fail => ret (Epsilon nil)
              | Epsilon v =>
                (** This is a bad grammar b/c it is doing epsilon*! **)
                ret Fail (* Epsilon (cons v nil) *)
              | Consume v rest pf =>
                bind (rec rest (R_l_len _ _ pf)) (fun r =>
                  match r with
                    | Fail => ret (Consume (cons v nil) rest pf)
                    | Epsilon vs => ret (Consume (cons v vs) rest pf)
                    | Consume vs rest pf' =>
                      let pf := RelationClasses.transitivity pf' pf in
                      ret (Consume (cons v vs) rest pf)
                  end)
            end)).

  Definition rec ls (env : @hlist _ (EParserT ls) ls) {T} (p : EParserT ls T) (n : nat)
    : ParserT T :=
    fun s =>
      let env :=
        (fix rec (n : nat) {struct n} : forall a : Type, member a ls -> ParserT a :=
          match n with
            | 0 => fun _ m => (hlist_get m env) (fun _ _ => fail)
            | S n => fun _ m => (hlist_get m env) (rec n)
          end) n
      in p env s.

  (** Derived Parsers **)

  Definition ignore {T} : ParserT T -> ParserT unit :=
    map (fun _ => ret tt).

  Definition surround {T U V} (b : ParserT T) (mid : ParserT U) (a : ParserT V) : ParserT U :=
    map (fun _m_ => ret (fst (snd _m_))) (seq b (seq mid a)).

End charset.

Section ascii_charset.
  Require Import String.

  Fixpoint list_to_string (ls : list ascii) : string :=
    match ls with
      | nil => EmptyString
      | l :: ls => String l (list_to_string ls)
    end.
  Fixpoint string_to_list (s : string) : list ascii :=
    match s with
      | EmptyString => nil
      | String s ss => s :: string_to_list ss
    end.

  Require Import ExtLib.Monad.IdentityMonad.

  Definition runParserS {T} (p : ParserT ascii ident T) (s : string) : option T :=
    unIdent (runParserT p (string_to_list s)).

  Definition lit (a : ascii) : ParserT ascii ident ascii :=
    satisfies (eq_dec a).

  Fixpoint in_dec {T} {RD : @RelDec T (@eq T)} (ls : list T) (v : T) : bool :=
    match ls with
      | nil => false
      | l :: ls =>
        if eq_dec v l then true else in_dec ls v
    end.

  Definition anyC (a : list ascii) : ParserT ascii ident ascii :=
    satisfies (in_dec a).

  (** Helper functions **)

  Definition TAB : ascii :=
    Ascii true false false true false false false false.
  Definition LF : ascii :=
    Ascii false true false true false false false false.
  Definition NULL : ascii :=
    Ascii false false false false false false false false.
  Definition SPACE : ascii := " "%char.

  (** Derived Parsers **)

  Definition space : ParserT ascii ident unit :=
    Eval cbv beta iota zeta delta [ string_to_list ] in
    ignore (anyC (string_to_list " ")).

  (** Tests **)

  Require Import ExtLib.Functor.Functor.
  Require Import ExtLib.Functional.Fun.

  Import FunctorNotation.
  Import FunNotation.

  Definition lparen : ParserT ascii ident ascii := lit "("%char.
  Definition rparen : ParserT ascii ident ascii := lit ")"%char.
  Definition a_star : ParserT ascii ident string := map (ret <$> list_to_string) (star (lit "a"%char)).

  Eval compute in runParserS (map (fun x => ret $ fst (snd x)) (seq lparen (seq a_star rparen))) "(aaaaaaaaaaa)"%string.

  Arguments HCons {iT} {F} (l) {ls} (_) (_).
  Arguments MZ {_} {_} {_}.
  Arguments MN {_} {_} {_} {_} (_).

  Definition ab_rec : ParserT ascii ident string :=
    let env := (string : Type) :: (string : Type) :: nil in
    let ps : hlist (EParserT ascii ident env) env :=
      HCons (F := EParserT ascii ident env) _ (fun get =>
        alt (map (fun x => ret $ String (fst x) (snd x)) (seq (lit "a"%char) (get _ (MN MZ))))
            (epsilon EmptyString))
      (HCons (F := EParserT ascii ident env) _ (fun get =>
        alt (map (fun x => ret $ String (fst x) (snd x)) (seq (lit "b"%char) (get _ MZ)))
            (epsilon EmptyString))
      (HNil (EParserT ascii ident env)))
    in
    @rec ascii ident _ env ps _ (fun get => get _ MZ) 10.

  Eval compute in runParserS ab_rec "ababababa"%string.
End ascii_charset.
