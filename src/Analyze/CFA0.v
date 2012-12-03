Require Import String List Bool.
Require Import CoqCompile.CpsK.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Monads.Fuel.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Programming.Show.
Require Import ExtLib.Data.Map.FMapAList.
Require Import CoqCompile.Analyze.AbstractDomains.

Import CpsK.CPSK.

Section Context_aware.
  Variable Context : Type.
  Context {AbsTime_c : AbsTime Context}.
  
  Definition AbstractLocation : Type := var.
  Inductive PtValue : Type :=
  | Int : BinNums.Z -> PtValue
  | Tpl : list Value -> PtValue
  | Clo : Context -> list cont -> list var -> exp -> PtValue
  with Value := 
  | Values : list PtValue -> Value (** use set **)
  | Any    : Value.
  
  Fixpoint val_leq (v1 v2:Value) : bool :=
    match v1, v2 with
      | Any, Any => true
      | Values vs1, Values vs2 =>
        List.fold_left (fun acc x => 
          match find (fun y => ptval_leq x y) vs2 with
            | None => false
            | Some _ => acc
          end) vs1 true
      | _, Any => true
      | _, _ => false
    end
  with ptval_leq (v1 v2:PtValue) : bool :=
    match v1, v2 with
      | Int _, Int _ => true
      | Tpl vs1, Tpl vs2 => 
        (fix fold_left2 acc ls1 ls2 :=
          match ls1, ls2 with
            | nil, nil => acc
            | x1::ls1, x2::ls2 =>
              if val_leq x1 x2 then acc else false
            | _, _ => false
          end) true vs1 vs2
      | Clo c1 ks1 xs1 e1, Clo c2 ks2 xs2 e2 =>
        rel_dec c1 c2 &&
        rel_dec ks1 ks2 &&
        rel_dec xs1 xs2 &&
        rel_dec e1 e2   
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
    fold_alist (fun k v acc => 
      match Maps.lookup k dom2 with
        | None => false
        | Some v' => val_leq v v'
      end
    ) true dom1
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
  
  Global Instance TplValue_Value : TplValue Value :=
  { injTuple := fun ls => Values (Tpl ls :: nil)
  ; projA    := fun n t =>
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
  }.

  Definition getClos (ls : list PtValue) : list (Context * list cont * list var * exp) :=
    filter_map (fun x =>
      match x with
        | Clo c xs vs e => Some (c, xs, vs, e)
        | _ => None
      end) ls.
  
  Global Instance FnValue_Value : FnValue Value Context Domain :=
  { injFn := fun c ks xs e => Values (Clo c ks xs e :: nil)
  ; applyA := fun _ _ aeval dom v ks vs' =>
    match v with
      | Any => ret dom (** TODO : think more about this! **)
      | Values vs =>
        let clos := getClos vs in
          foldM (fun x acc => let '(c, ks', xs', e) := x in
          if eq_dec (List.length ks') (List.length ks) &&
             eq_dec (List.length xs') (List.length vs) then
            let ext := List.combine (List.map (fun x => inr x) ks') ks 
                    ++ List.combine (List.map (fun x => inl x) xs') vs' in
            let dom' := fold_left (fun acc x => update c (fst x) (snd x) acc) ext dom in 
              aeval c dom' e
            else
              ret acc) (ret dom) clos
    end
  }.

End Context_aware.