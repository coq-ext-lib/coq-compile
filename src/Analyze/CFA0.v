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
Require Import ExtLib.Programming.Show.

Import CpsK.CPSK.

Section CFA0.

  Global Instance AbsTime_unit : AbsTime unit :=
  { ED := _ }.

End CFA0.

Section Context_aware.
  Variable Context : Type.
  Context {AbsTime_c : AbsTime Context}.
  
  Definition aLoc : Type := var.

  Inductive PtValue : Type :=
  | Ctor : constructor -> PtValue
  | Int : BinNums.Z -> PtValue
  | Tpl : aLoc -> PtValue
  | Clo : Context -> (var + cont) -> list cont -> list var -> exp -> PtValue
  with Value := 
  | Values : list PtValue -> Value (** use set **)
  | Any    : Value.

  Section hide_notation.
    Import ShowNotation.
    Local Open Scope show_scope.
    Local Open Scope string_scope.
    
    Fixpoint show_ptval (pv:PtValue) : showM :=
      match pv with
        | Ctor c => c
        | Int z => show z
        | Tpl l => show l
        | Clo c v ks xs e => "<closure>" << show v
      end
    with show_val (v:Value) : showM :=
      match v with
        | Values vs => "{" << sepBy_f show_ptval "," vs << "}"
        | Any => "any"
      end.
    Global Instance Show_Value : Show Value := show_val.
    Global Instance Show_PtValue : Show PtValue := show_ptval.

  End hide_notation.

  Fixpoint val_leq (v1 v2:Value) : bool :=
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
    end
  with ptval_leq (v1 v2:PtValue) : bool :=
    match v1, v2 with
      | Ctor c1, Ctor c2 => eq_dec c1 c2
      | Int _, Int _ => true
      | Tpl l1, Tpl l2 => eq_dec l1 l2
        (*
        (fix fold_left2 acc ls1 ls2 :=
          match ls1, ls2 with
            | nil, nil => acc
            | x1::ls1, x2::ls2 =>
              if val_leq x1 x2 then acc else false
            | _, _ => false
          end) true vs1 vs2
        *)
      | Clo c1 v1 ks1 xs1 e1, Clo c2 v2 ks2 xs2 e2 =>
        eq_dec c1 c2 &&
        eq_dec ks1 ks2 &&
        eq_dec xs1 xs2 &&
        eq_dec e1 e2   
      | _, _ => false
    end.

  Definition Domain : Type := alist (var + cont) Value.
  Definition ProgramPoint : Type := (var + cont)%type.
  
  Definition bottomValue : Value := Values nil.
  
  Definition joinValue (v1 v2 : Value) : Value :=
    match v1 , v2 with
      | Any , _ => Any
      | _ , Any => Any
      | Values x , Values y => Values (x ++ y)
    end.
  
  Global Instance AbsDomain_CFA0 : AbsDomain Domain Value Context ProgramPoint :=
  { lookup  := fun c p d => 
    match Maps.lookup p d with
      | None => bottomValue
      | Some v => v
    end
  ; update  := fun c p v d =>
    match Maps.lookup p d with
      | None => Maps.add p v d
      | Some v_old => Maps.add p (joinValue v_old v) d
    end
  ; joinA   := Maps.combine (fun _ => joinValue) 
  ; bottomA := bottomValue
  ; topA    := Any
  ; dom_leq   := fun dom1 dom2 => 
    fold_alist (fun k v (acc : bool) => 
      if acc then 
        match Maps.lookup k dom2 with
          | None => false
          | Some v' => val_leq v v'
        end
      else false) true dom1
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
  { injCtor := fun x => Any (* Values (Ctor x :: nil) *)
  ; isPtrA := fun _ => None
  ; ceqA := fun _ _ => None
  }.

  Global Instance BoolValue_Value : BoolValue Value :=
  { injBool := fun x => Any
  ; may := fun _ _ => true
  ; must := fun _ _ => false
  ; orA := fun _ _ => Any      
  }.

  Fixpoint list_join_lenAny (ls ls' : list Value) : list Value :=
    match ls , ls' with
      | nil , ls' => ls'
      | ls , nil => ls
      | l :: ls , l' :: ls' =>
        joinValue l l' :: list_join_lenAny ls ls'
    end.
  
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

  Import MonadNotation.
  Local Open Scope monad_scope.
  Require Import ExtLib.Data.Monads.StateMonad.

  Global Instance TplValue_Value : TplValue Value (list Value) :=
  { injTuple := fun _ _ _ v ls => Values (Tpl v :: nil) (* Values (Tpl ls :: nil) *)
  ; projA    := fun _ _ _ n t => _
    (*
    match t with
      | Any => Any
      | Values vs =>
        let ptwise_tuple := List.fold_left (fun acc x => 
          match x with
            | Tpl vs => list_join_lenAny vs acc
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
    *)
  }.  
  refine (
    match t with
      | Any => Any
      | Values vs =>
        let alocs := List.fold_left (fun acc x => 
          match x with
            | Tpl l => l::acc
            | _ => acc
          end) vs nil in
        match n with
          | Any => _ (* TODO : lookup from the abstract heap the joins of all the alocs *)
          | Values v => 
            let nats := getNats v in _
              (* TODO : lookup from the abstract heap the join of all the alocs at the nth position *)
        end
    end
  ).
  (* wtf monad troubles ... *)

  Definition getClos (ls : list PtValue) : list (Context * list cont * list var * exp) :=
    filter_map (fun x =>
      match x with
        | Clo c v xs vs e => Some (c, xs, vs, e)
        | _ => None
      end) ls.

  Local Open Scope monad_scope.
  Import MonadNotation.
  Require Import CoqCompile.TraceMonad.
  
  Check @foldM.

  Global Instance FnValue_Value : FnValue (var + cont) Value Context Domain :=
  { injFn := fun c v ks xs e => Values (Clo c v ks xs e :: nil)
  ; applyA := fun _ _ _ aeval dom v ks vs' =>
    match v with
      | Any => 
        mlog "YIKES"%string ;; ret dom (** TODO : think more about this! **)
      | Values vs =>
        let clos := getClos vs in
        foldM (fun x acc => let '(c, ks', xs', e) := x in
          if eq_dec (List.length ks') (List.length ks) &&
             eq_dec (List.length xs') (List.length vs') then
            let ext := List.combine (List.map (fun x => inr x) ks') ks 
                    ++ List.combine (List.map (fun x => inl x) xs') vs' in
            let dom' := fold_left (fun acc x => update c (fst x) (snd x) acc) ext acc in 
            aeval c dom' e
          else
            mlog ("HERE " ++ (to_string (ks, ks')) ++ " " ++ (to_string (vs, xs')))%string ;;
            ret acc) (ret dom) clos
    end
  }.

End Context_aware.

Require Import CoqCompile.Analyze.AbstractInterpCpsK.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Data.Monads.FuelMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import CoqCompile.TraceMonad.
Require Import BinNums.
Definition cfa_0 (e:exp) (fuel:N) : ((string + Domain unit) * list string).
refine (let pcfa := aeval (Domain unit) unit _ (traceT string ident) tt in _).
unfold Domain in *.
refine (unIdent (traceTraceT (pcfa Maps.empty e fuel))).
Defined.

  Global Instance Show_Domain_unit : Show (Domain unit) :=
  { show := _ }.
  unfold Domain. eauto with typeclass_instances.
  Defined.


Module CFA0_test.
  Require Import String List Bool.
  Require Import CoqCompile.Parse.
  Require CoqCompile.CpsKConvert.

  Definition f := fun (x:nat) => x.

  Definition test1 := 
    f 1.

  Extraction Language Scheme.
  Recursive Extraction test1.

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
  Definition test2 := g (h 1) 1.

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

  Eval vm_compute in
    let '(r,tr) := (cfa_0 test2_cpsk 4) in
      to_string (sepBy Char.chr_newline (List.map show tr)).
  Eval vm_compute in to_string test2_cpsk.

End CFA0_test.