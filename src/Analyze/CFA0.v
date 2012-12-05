Require Import String List Bool.
Require Import CoqCompile.CpsK.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Map.FMapAList.
Require Import CoqCompile.Analyze.AbstractDomains.
Require Import ExtLib.Data.Set.ListSet.
Require Import ExtLib.Programming.Show.

Import CpsK.CPSK.

Section Context_parametric.
  Variable Context : Type.
  Context {AbsTime_c : AbsTime Context (var + cont)}.

  Instance RelDec_C : RelDec (@eq Context).
  eapply ED; eassumption.
  Defined.
  
  Definition aLoc : Type := var.
  Definition ProgramPoint : Type := (var + cont)%type.

  Inductive PtValue : Type :=
  | Ctor : constructor -> PtValue
  | Int : BinNums.Z -> PtValue
  | Ptr : aLoc -> PtValue
  | Clo : Context -> ProgramPoint -> list cont -> list var -> exp -> PtValue.

  Global Instance RelDec_PtValue : RelDec (@eq PtValue) :=
  { rel_dec := fun v1 v2 => 
    match v1, v2 with
      | Ctor c1, Ctor c2 => eq_dec c1 c2
      | Int i1, Int i2 => eq_dec i1 i2
      | Ptr l1, Ptr l2 => eq_dec l1 l2
      | Clo c1 pp1 ks1 xs1 e1, Clo c2 pp2 ks2 xs2 e2 =>
        eq_dec c1 c2 &&
        eq_dec pp1 pp2 &&
        eq_dec ks1 ks2 &&
        eq_dec xs1 xs2 &&
        eq_dec e1 e2
      | _, _ => false
    end}.

  Inductive Value : Type := 
  | Values : lset (@eq PtValue) -> Value (** use set **)
  | Any    : Value.

  Section hide_notation.
    Import ShowNotation.
    Local Open Scope show_scope.
    Local Open Scope string_scope.
    
    Global Instance Show_ptval : Show PtValue :=
    { show := fun (pv:PtValue) =>
      match pv with
        | Ctor c => c
        | Int z => show z
        | Ptr aLoc => show aLoc
        | Clo c v ks xs e => "<closure " << show v << ">"
      end }.

    Global Instance Show_val : Show Value :=
    { show := fun (v:Value) =>
      match v with
        | Values vs => "{" << sepBy_f show "," vs << "}"
        | Any => "any"
      end }.

  End hide_notation.

  Definition ptval_leq (v1 v2:PtValue) : bool :=
    match v1, v2 with
      | Ctor c1, Ctor c2 => eq_dec c1 c2
      | Int i1, Int i2 => eq_dec i1 i2
      | Ptr l1, Ptr l2 => eq_dec l1 l2
      | Clo c1 v1 ks1 xs1 e1, Clo c2 v2 ks2 xs2 e2 =>
        eq_dec c1 c2 &&
        eq_dec ks1 ks2 &&
        eq_dec xs1 xs2 &&
        eq_dec e1 e2
      | _, _ => false
    end.

  Fixpoint all2 {A} (f : A -> A -> bool) (ls ls' : list A) : bool :=
    match ls , ls' with
      | nil , ls' => true
      | ls , nil => false
      | l :: ls , l' :: ls' =>
        if f l l' then all2 f ls ls' else false
    end.

  Definition val_leq (v1 v2:Value) : bool :=
    match v1, v2 with
      | Any, Any => true
      | Values vs1, Values vs2 =>
        List.fold_left (fun acc x => 
          match List.find (fun y => ptval_leq x y) vs2 with
            | None => false
            | Some _ => acc
          end) vs1 true
      | _, Any => true
      | _, _ => false
    end.

  (* heap and environment *)
  Record Domain : Type := 
  { heap : alist (Context * aLoc) (list Value)
  ; env  : alist (Context * ProgramPoint) Value }.
  
  Definition bottomValue : Value := Values nil.
  
  Definition joinValue (v1 v2 : Value) : Value :=
    match v1 , v2 with
      | Any , _ => Any
      | _ , Any => Any
      | Values x , Values y => Values (Sets.union x y)
    end.
  
  Definition dom_env_leq (dom1 dom2 : Domain) : bool :=
    let dom1 := env dom1 in
    let dom2 := env dom2 in
    fold_alist (fun k v (acc : bool) => 
      if acc then 
        match Maps.lookup k dom2 with
          | None => false
          | Some v' => val_leq v v'
        end
      else false) true dom1.

  Definition dom_heap_leq (dom1 dom2 : Domain) : bool :=
    let dom1 := heap dom1 in
    let dom2 := heap dom2 in
    fold_alist (fun k v (acc : bool) => 
      if acc then 
        match Maps.lookup k dom2 with
          | None => false
          | Some v' => all2 val_leq v v'
        end
      else false) true dom1.

  Fixpoint list_join_lenAny (ls ls' : list Value) : list Value :=
    match ls , ls' with
      | nil , ls' => ls'
      | ls , nil => ls
      | l :: ls , l' :: ls' =>
        joinValue l l' :: list_join_lenAny ls ls'
    end.

  Global Instance AbsDomain_CFA0 : AbsDomain Context Domain ProgramPoint Value :=
  { lookup  := fun c p d => 
    match Maps.lookup (c,p) (env d) with
      | None => bottomValue
      | Some v => v
    end
  ; update  := fun c p v d =>
    {| heap := heap d ;
       env :=
       match Maps.lookup (c,p) (env d) with
         | None => Maps.add (c,p) v (env d)
         | Some v_old => 
           Maps.add (c,p) (joinValue v_old v) (env d)
       end |}
  ; joinA   := fun d1 d2 =>
    {| heap := Maps.combine (fun _ => list_join_lenAny) (heap d1) (heap d2);
       env := Maps.combine (fun _ => joinValue) (env d1) (env d2) |} 
  ; bottomA := bottomValue
  ; topA    := Any
  ; dom_leq   := fun dom1 dom2 => dom_env_leq dom1 dom2 && dom_heap_leq dom1 dom2
  }.
  
  Global Instance IntValue_Value : IntValue Value :=
  { injInt := fun v => 
    match v with 
      | None => Any
      | Some v => Values (Int v :: nil)
    end
  ; plusA  := fun x y => Any
  ; minusA := fun x y => Any
  ; timesA := fun x y => Any
  ; eqA    := fun _ _ => None
  ; ltA    := fun _ _ => None
  }.

  Global Instance CtorValue_Value : CtorValue Value constructor :=
  { injCtor := fun x => Values (Ctor x :: nil)
  ; isPtrA := fun _ => None
  ; ceqA := fun _ _ => None
  }.

  Global Instance BoolValue_Value : BoolValue Value :=
  { injBool := fun x => Any
  ; may := fun _ _ => true
  ; must := fun _ _ => false
  ; orA := fun _ _ => Any      
  }.
  
  Fixpoint filter_map {A B} (f : A -> option B) (ls : list A) : list B :=
    match ls with
      | nil => nil
      | l :: ls => 
        match f l with
          | None => filter_map f ls
          | Some v => v :: filter_map f ls
        end
    end.
  
  Definition getNats (ls : list PtValue) : list nat :=
    filter_map (fun x =>
      match x with
        | Int BinNums.Z0 => Some 0
        | Int (BinNums.Zpos n) => Some (BinPos.Pos.to_nat n)
        | _ => None
      end) ls.

  Global Instance TplValue_Value : TplValue Context Domain Value :=
  { injTuple := fun dom ctx v ls =>
    {| env := env (update ctx (inl v) (Values (Sets.singleton (Ptr v))) dom);
       heap :=
       match Maps.lookup (ctx,v) (heap dom) with
         | None => Maps.add (ctx,v) ls (heap dom)
         | Some ls_old => 
           Maps.add (ctx,v) (list_join_lenAny ls_old ls) (heap dom)
       end |}
  ; projA    := fun dom ctx n t =>
    match t with
      | Any => Any
      | Values vs =>
        let ptwise_tuple := List.fold_left (fun acc x => 
          match x with
            | Ptr l => match Maps.lookup (ctx, l) (heap dom) with
                         | None => acc
                         | Some vs => list_join_lenAny vs acc
                       end
            | _ => acc
          end) vs nil in
        match n with
          | Any => List.fold_left joinValue ptwise_tuple bottomA
          | Values v => 
            let nats := getNats v in
            let all := List.map (fun n => 
              match nth_error ptwise_tuple n with
                | None => bottomA
                | Some x => x
              end) nats in
            List.fold_left joinValue all bottomA
        end
    end
  }.  

  Definition getClos (ls : list PtValue) : list (Context * ProgramPoint * list cont * list var * exp) :=
    filter_map (fun x =>
      match x with
        | Clo c v xs vs e => Some (c, v, xs, vs, e)
        | _ => None
      end) ls.

  Local Open Scope monad_scope.
  Import MonadNotation.
  Require Import CoqCompile.TraceMonad.
 
  Global Instance FnValue_Value : FnValue Context Domain (var + cont) Value :=
  { injFn := fun c v ks xs e => Values (Clo c v ks xs e :: nil)
  ; applyA := fun _ _ _ _ aeval dom v ks vs' =>
    match v with
      | Any => 
        mlog "YIKES"%string ;; ret dom (** TODO : think more about this! **)
      | Values vs =>
        let clos := getClos vs in
        foldM (fun x acc => let '(c, pp, ks', xs', e) := x in
          if eq_dec (List.length ks') (List.length ks) &&
             eq_dec (List.length xs') (List.length vs') then
            let ext := List.combine (List.map (fun x => inr x) ks') ks 
                    ++ List.combine (List.map (fun x => inl x) xs') vs' in
            let dom' := fold_left (fun acc x => update c (fst x) (snd x) acc) ext acc in 
            aeval (enter c pp) dom' e
          else
            mlog ("HERE " ++ (to_string (ks, ks')) ++ " " ++ (to_string (vs, xs')))%string ;;
            ret acc) (ret dom) clos
    end
  }.

End Context_parametric.

Section Context.

  Variable A : Type.
  Context {RelDec_A : RelDec (@eq A)}.
  
  Fixpoint context (n : nat) : Type :=
    match n with
      | 0 => unit
      | S n => option (A * context n)
    end.
  
  Definition init_ctx (n : nat) : context n :=
    match n with
      | 0 => tt
      | S n => None
    end.

  Section hiding_notation.
    Import ShowNotation.
    Local Open Scope show_scope.
    Local Open Scope string_scope.

    Fixpoint show_context_n (S : Show A) (n : nat) : context n -> showM :=
      match n as n return context n -> showM with
        | 0 => fun _ => "()"
        | S n => fun c => 
          match c with
            | None => "()"
            | Some (p,c) => "(" << show p << "," << show_context_n _ _ c
          end
      end.
    
    Global Instance Show_context n (S : Show A) : Show (context n) :=
    { show c := "<ctx " << show_context_n _ _ c << ">" }.
  End hiding_notation.

  Definition enter_ctx (n : nat) : context n -> A -> context n :=
    (fix enter {B} (n : nat) : (context n -> B) -> context n -> A -> B :=
      match n as n return (context n -> B) -> context n -> A -> B with 
        | 0 => fun k _ _ => k tt
        | S n => fun k ctx pp => 
          match ctx with
            | None => k (Some (pp, init_ctx _))
            | Some (pp',ctx') => enter _ (fun c => k (Some (pp, c))) ctx' pp 
          end
      end) _ n (fun x => x).

  Instance RelDec_context n : RelDec (@eq (context n)).
  induction n ; eauto with typeclass_instances.
  Defined.
 
  Definition AbsTime_0 {A} : AbsTime unit A :=
  {| ED := _ 
   ; enter := fun c p => c
   |}.

  Global Instance AbsTime_n n : AbsTime (context n) A :=
  {| ED := _ 
   ; enter := enter_ctx n
   |}.

End Context.

Section hiding_notation.
  Import ShowNotation.
  Local Open Scope show_scope.
  Local Open Scope string_scope.

  Global Instance Show_Domain C (SC : Show C) : Show (Domain C) :=
  { show d := Char.chr_newline << "Heap: " << Char.chr_newline <<
    sepBy_f (fun kv => show (fst kv) << " : " << show (snd kv)) Char.chr_newline (heap _ d) <<
    Char.chr_newline << Char.chr_newline <<
    "Env: " << Char.chr_newline <<
    sepBy_f (fun kv => show (fst kv) << " : " << show (snd kv)) Char.chr_newline (env _ d) <<
    Char.chr_newline }.
End hiding_notation.

Require Import CoqCompile.Analyze.AbstractInterpCpsK.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Data.Monads.FuelMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import CoqCompile.TraceMonad.
Require Import BinNums.

Definition cfa_n (n : nat) (e:exp) (fuel:N) : ((string + Domain (context (var + cont) n)) * list string) :=
  let ctx := context (var + cont) n in
  let pcfa := aeval (AbsTime_C := AbsTime_n _ n)
    (D := Domain ctx) (C := ctx) (V := Value ctx) (m := traceT string ident) 
    (init_ctx _ n) 
    {| heap := Maps.empty ; env := Maps.empty |} e fuel in 
  unIdent (traceTraceT pcfa).

(*
Module CFA0_test.
  Require Import String List Bool.
  Require Import CoqCompile.Parse.
  Require CoqCompile.CpsKConvert.

  Definition f := fun (x:nat) => x.

  Definition test1 := 
    f 1.

(*
  Extraction Language Scheme.
  Recursive Extraction test1.
*)

  Definition test1_s := 
    "(define f (lambda (x) x))

    (define test1 (f `(S ,`(O))))"%string.

  Definition test1_lam :=
    Eval vm_compute in 
      Parse.parse_topdecls test1_s.

  Definition test1_cpsk : CPSK.exp :=
    Eval vm_compute in
      match test1_lam as plus_e return match plus_e with
                                        | inl _ => unit
                                        | inr x => CPSK.exp
                                      end with
        | inl _ => tt
        | inr e => CpsKConvert.CPS_pure e 
      end.
  
  Definition g := fun (x y:nat) => x.
  Definition h := fun (x : nat) => S x.
  Definition test2 := g (h (h 1)) 1.

  Recursive Extraction test2.
  Definition test2_s :=
    "(define g (lambdas (x y) x))

(define h (lambda (x) `(S ,x)))

(define test2 (@ g (h (h `(S ,`(O)))) `(S ,`(O))))"%string.
  
  Definition test2_lam :=
    Eval vm_compute in 
      Parse.parse_topdecls test2_s.

  Definition test2_cpsk : CPSK.exp :=
    Eval vm_compute in
      match test2_lam as plus_e return match plus_e with
                                        | inl _ => unit
                                        | inr x => CPSK.exp
                                      end with
        | inl _ => tt
        | inr e => CpsKConvert.CPS_pure e 
      end.

  Require Import CpsKExamples.

  Import ShowNotation.
  Local Open Scope show_scope.
  Global Instance Show_showM : Show showM :=
    fun x => x.

  Time Eval vm_compute in
    let '(r,tr) := (cfa_n 0 test2_cpsk 10) in to_string r.

  Eval vm_compute in to_string test2_cpsk.

  Eval vm_compute in
    let '(r,tr) := (cfa_0 test2_cpsk 10) in
      to_string (sepBy Char.chr_newline (List.map show tr)).

End CFA0_test.
*)
