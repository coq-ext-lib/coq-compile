Require Import List.
Require Import Ascii.
Require Import ExtLib.Data.HList ExtLib.Data.Strings.
Require Import ExtLib.Rec.GenRec. 
Require Import ExtLib.Decidables.Decidable.

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

  Definition Parser (T : Type) : Type :=
    forall s : stream, Parse s T.

  Definition runParser {T} (p : Parser T) (s : stream) : option T :=
    match p s with
      | Fail => None
      | Epsilon v => Some v
      | Consume v _ _ => Some v
    end.

  Definition fail {T : Type} : Parser T :=
    fun _ => Fail.

  Definition map {T U} (f : T -> U) (p : Parser T) : Parser U :=
    fun s =>
      match p s with
        | Fail => Fail
        | Epsilon v => Epsilon (f v)
        | Consume v rest pf => Consume (f v) rest pf
      end.

  Definition satisfies (f : Tok -> bool) : Parser Tok :=
    fun s => 
      match s with 
        | nil => Fail
        | a' :: s => 
          if f a' then Consume a' s (le_n (length (a' :: s)))
          else Fail
      end.

  Definition epsilon {T : Type} (v : T) : Parser T :=
    fun _ => Epsilon v.

  Definition seq {T} (p1 : Parser T) {U} (p2 : Parser U) : Parser (T * U) :=
    fun s =>
      match p1 s with
        | Fail => Fail
        | Epsilon v => 
          match p2 s with
            | Fail => Fail
            | Epsilon u => Epsilon (v,u)
            | Consume u rest pf => Consume (v, u) _ pf
          end
        | Consume v rest pf =>
          match p2 rest with
            | Fail => Fail
            | Epsilon u => Consume (v, u) _ pf
            | Consume u rest pf' => 
              let pf := RelationClasses.transitivity pf' pf in
                Consume (v, u) _ pf
          end
      end.

  Definition alt {T} (p1 p2 : Parser T) : Parser T :=
    fun s => 
      match p1 s with
        | Fail => p2 s
        | x => x
      end.

  Definition EParser (ls : list Type) (T : Type) :=
    (forall a, member a ls -> Parser a) -> Parser T.

  Definition star {T} (p : Parser T) : Parser (list T).
  red. eapply Fix. eapply wf_R_list_len.
  refine (fun x rec => match p x with
            | Fail => Epsilon nil
            | Epsilon v =>
              (** This is a bad grammar b/c it is doing epsilon*! **)
              Fail (* Epsilon (cons v nil) *)
            | Consume v rest pf =>
              match rec rest (R_l_len _ _ pf) with
                | Fail => Consume (cons v nil) rest pf
                | Epsilon vs => Consume (cons v vs) rest pf
                | Consume vs rest pf' => 
                  let pf := RelationClasses.transitivity pf' pf in
                    Consume (cons v vs) rest pf
              end
          end).
  Defined.

  Definition rec ls (env : @hlist _ (EParser ls) ls) {T} (p : EParser ls T) (n : nat) : Parser T.
  red.
  refine (fun s => 
    p _ s).
  refine ((fix rec (n : nat) {struct n} : forall a : Type, member a ls -> Parser a :=
    match n with
      | 0 => fun _ m => (get m env) (fun _ _ => fail)
      | S n => fun _ m => (get m env) (rec n)
    end) n).
  Defined.

  (** Derived Parsers **)
  Definition ignore {T} : Parser T -> Parser unit :=
    map (fun _ => tt).

  Definition surround {T U V} (b : Parser T) (mid : Parser U) (a : Parser V) : Parser U :=
    map (fun _m_ => fst (snd _m_)) (seq b (seq mid a)).

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

  Definition runParserS {T} (p : Parser ascii T) (s : string) : option T :=
    runParser p (string_to_list s).

  Definition lit (a : ascii) : Parser ascii ascii :=
    satisfies (eq_dec a).

  Fixpoint in_dec {T} {RD : @RelDec T (@eq T)} (ls : list T) (v : T) : bool :=
    match ls with
      | nil => false
      | l :: ls => 
        if eq_dec v l then true else in_dec ls v
    end.

  Definition anyC (a : list ascii) : Parser ascii ascii :=
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

  Definition space : Parser ascii unit :=
    Eval cbv beta iota zeta delta [ string_to_list ] in
    ignore (anyC (string_to_list " ")).

  (** Tests **)

  Definition lparen : Parser ascii ascii := lit "("%char.
  Definition rparen : Parser ascii ascii := lit ")"%char.
  Definition a_star : Parser ascii string := map list_to_string (star (lit "a"%char)).

  Eval compute in runParserS (map (fun x => fst (snd x)) (seq lparen (seq a_star rparen))) "(aaaaaaaaaaa)"%string.

  Arguments HCons {iT} {F} (l) {ls} (_) (_).
  Arguments MZ {_} {_} {_}.
  Arguments MN {_} {_} {_} {_} (_).

  Definition ab_rec : Parser ascii string :=
    let env := (string : Type) :: (string : Type) :: nil in
    let ps : hlist (EParser ascii env) env :=
      HCons (F := EParser ascii env) _ (fun get => 
        alt (map (fun x => String (fst x) (snd x)) (seq (lit "a"%char) (get _ (MN MZ))))
            (epsilon EmptyString))
      (HCons (F := EParser ascii env) _ (fun get => 
        alt (map (fun x => String (fst x) (snd x)) (seq (lit "b"%char) (get _ MZ)))
            (epsilon EmptyString))
      (HNil (EParser ascii env)))
    in
    @rec ascii env ps _ (fun get => get _ MZ) 10.

  Eval compute in runParserS ab_rec "ababababa"%string.
End ascii_charset.