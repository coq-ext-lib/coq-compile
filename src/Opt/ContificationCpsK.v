Require Import String List.
Require Import CoqCompile.CpsK.
Require Import CoqCompile.CpsKUtil.
Require Import ExtLib.ExtLib.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Sets.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Set.ListSet.
Require Import ExtLib.Data.Map.FMapAList.

Set Implicit Arguments.
Set Strict Implicit.

Section map_monoid.
  Variable M : Type -> Type.
  Variable K : Type.
  Variable E : Type.
  Variable Monoid_e : Monoid E.
  Context {DMap_M : DMap K M}.
  Context {Foldable_M : Foldable (M E) (K * E)}.   

  Definition Monoid_map : Monoid (M E) :=
  {| monoid_unit := Maps.empty
   ; monoid_plus := Maps.combine (K := K) (fun _ => monoid_plus Monoid_e)
  |}.
End map_monoid.


Module Contify.
  
  Import CpsK.CPSK.


  (** A function [f] can be made into a continuation [k] if all execution
   ** paths in [f] return to the same continuation.
   **
   ** Further: The function must be in the scope of the continuation (can I move it?).
   ** In particular, this means that I can not contify a function inside a function
   ** if I know that it refers to the outer continuation.
   ** - My analysis should never say that I can do this because we always do return
   **   to a passed-in continuation
   **)

  Definition map_monoid : Monoid (alist var (lset (@eq (list cont)))) := 
      @Monoid_map (alist var) _ _ (@Monoid_set_union _ _ _ _) _ _.

  Definition set_monoid := @Monoid_set_union (lset (@eq var)) _ _ _.

  Section monadic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {Contexts_m : MonadWriter map_monoid m}.
    Context {Escapes_m : MonadWriter set_monoid m}.
    Context {MonadExc_m : MonadExc string m}.
    Context {ContSubst_m : MonadReader (alist cont cont) m}.

    Definition call (f : op) (ks : list cont) : m unit :=
      match f with
        | Var_o f =>
          tell (Maps.singleton f (Sets.singleton ks))
        | _ => raise "Calling non-variable"%string
      end.

    Definition escapes (o : op) : m unit :=
      match o with
        | Var_o v => tell (Sets.singleton v)
        | _ => ret tt
      end.

    Import MonadNotation.
    Local Open Scope monad_scope.

    Definition isSingleton {A} (ls : lset (@eq A)) : option A :=
      match ls with
        | x :: nil => Some x
        | _ => None
      end.
    
    Fixpoint replaceCalls (f : op) (k : cont) (e : exp) : exp :=
      match e with
        | App_e f' ks xs => if eq_dec f f' then AppK_e k xs else e
        | AppK_e _ _ => e
        | Halt_e _ _ => e
        | Let_e d e => Let_e d (replaceCalls f k e)
        | LetK_e ks e =>
          let ks' := map (fun kxse => let '(k,xs,e) := kxse in
            (k, xs, replaceCalls f k e)) ks
          in 
          LetK_e ks' (replaceCalls f k e)
        | Letrec_e ds e =>
          Letrec_e ds (replaceCalls f k e)
        | Switch_e o arms def =>
          let arms' := map (fun x => (fst x, replaceCalls f k (snd x))) arms in
          let def' := map (replaceCalls f k) def in
          Switch_e o arms' def'
      end.

    Definition replaceAllCalls (cs : list (op * cont)) (e : exp) : exp :=
      List.fold_left (fun acc e_c => let '(f,c) := e_c in 
        replaceCalls f c acc) cs e.

    Definition var_to_cont (v : var) : m cont :=
      ret match v with 
            | Anon_v p => K "" p
            | Named_v s None => K s 1
            | Named_v s (Some p) => K s p
          end.

    Definition contify_k (k : cont) : m cont :=
      k' <- asks (Maps.lookup k) ;;
      match k' with
        | None => ret k
        | Some k => ret k
      end.
        
    Fixpoint withConts {T} (ks ks' : list cont) (c : m T) : m T :=
      match ks , ks' with
        | nil , nil => c
        | k :: ks , k' :: ks' => local (Maps.add k k') (withConts ks ks' c)
        | _ , _ => raise "inconsistent continutations "%string
      end.

    Definition mark_escapes (rec : bool) (d : decl) : m unit :=
      let fvars : lset (@eq (var + cont)) := free_vars_decl rec d in
      iterM (fun x => match x with
                        | inl v => escapes (Var_o v)
                        | _ => ret tt
                      end) fvars.

    Definition remove_escapes {T} (ls : list var) (c : m T) : m T :=
      censor (List.fold_left (fun acc v => Sets.remove v acc) ls) c.

    Definition remove_calls {T} (ls : list var) (c : m T) : m T :=
      censor (List.fold_left (fun acc v => Maps.remove v acc) ls) c.

    Definition contifiable (f : var) (escapes : lset (@eq var)) (calls : alist var (lset (@eq (list cont)))) : option (list cont) :=
      if Sets.contains f escapes then None
      else match Maps.lookup f calls with
             | None => Some nil (** it isn't used and it doesn't escape, it is dead code **)
             | Some calls => isSingleton calls
           end.
             

    Fixpoint contify_exp (e : exp) : m exp.
    refine (
      match e with
        | AppK_e k xs =>
          iterM escapes xs ;;
          k <- contify_k k ;;
          ret (AppK_e k xs)
        | App_e f ks xs => 
          iterM escapes xs ;;
          ks <- mapM contify_k ks ;;
          call f ks ;;
          ret (App_e f ks xs)
        | Halt_e x w =>
          ret (Halt_e x w) 
        | Switch_e o arms def =>
          arms' <- mapM (fun pe => let '(p,e) := pe in 
            e' <- contify_exp e ;;
            ret (p, e')) arms ;;
          def' <- mapM contify_exp def ;;
          ret (Switch_e o arms' def')
        | Let_e (Fn_d f ks xs e_body) e =>
          e'_conts <- remove_escapes xs (censor (Maps.remove f) (listen (MonadWriter := Escapes_m) (listen (MonadWriter := Contexts_m) (contify_exp e)))) ;;
          let '(e',calls,escape_vars) := e'_conts in
          let contifiable := contifiable f escape_vars calls in
          match contifiable with
            | None =>
              e_body' <- contify_exp e_body ;;
              mark_escapes false (Fn_d f ks xs e_body') ;;
              ret (Let_e (Fn_d f ks xs e_body') e')
            | Some args =>
              (** We can contify f **)
              k <- var_to_cont f ;;
              let e' := replaceCalls (Var_o f) k e' in
              e_body' <- withConts ks args (contify_exp e_body) ;;
              ret (LetK_e ((k, xs, e_body') :: nil) e')
          end
        | Let_e d e => 
          mark_escapes false d ;;
          e' <- contify_exp e ;;
          ret (Let_e d e')
        | Letrec_e ds e =>
          e' <- contify_exp e ;;
          let names := List.map (fun d => match d with
                                            | Fn_d v _ _ _
                                            | Prim_d v _ _ 
                                            | Op_d v _ 
                                            | Bind_d v _ _ _ => v
                                         end) ds in
          (** Only consider for contification if it contains only functions **)
          let has_non_func := List.fold_left (fun acc d => match d with
                                                             | Fn_d _ _ _ _ => acc
                                                             | _ => true
                                                           end) ds false in
          if has_non_func then
            (** mark the escapes and return **)
            iterM (mark_escapes true) ds ;;
            ret (Letrec_e ds e')
          else
            func_names <- mapM (fun d => match d with
                                           | Fn_d v _ _ _ => ret v 
                                           | _ => raise "unreachable"%string
                                         end) ds ;;
            e'_conts <- remove_escapes func_names (remove_calls func_names (listen (listen (
              ds <- mapM (fun d =>
                match d with
                  | Fn_d v ks xs e => 
                    e' <- remove_escapes xs (contify_exp e) ;;
                    ret (Fn_d v ks xs e)
                  | _ => raise "unreachable"%string
                end) ds ;;
              e' <- contify_exp e ;;
              ret (ds, e')
            )))) ;;
            let '((ds',e'),conts,escape_vars) := e'_conts in
            (** we can contify if all ds are contifiable **)
            (fix continue (ds : list decl) (ks' : list (var * list var * exp)) :=
              match ds with
                | nil => 
                  (** We can contify the let rec **)
                  ks'' <- mapM (fun f => let '(f,_,_) := f in 
                                 k' <- var_to_cont f ;;
                                 ret (Var_o f, k')) ks' ;;
                  let _ : alist op cont := ks'' in
                  ks' <-
                    mapM (fun kxse => let '(f,xs,e) := kxse in
                      match Maps.lookup (Var_o f) ks'' with
                        | None => raise "unreachable"%string
                        | Some k => ret (k, xs, replaceAllCalls ks'' e)
                      end) ks' ;;
                  ret (LetK_e ks' (replaceAllCalls ks'' e'))
                | Fn_d v ks xs e :: ds =>
                  match contifiable v conts escape_vars with
                    | None =>
                      (** can't contify **)
                      ret (Letrec_e ds' e')
                    | Some args =>
                      continue ds ((v, xs, e) :: ks')
                  end
                | _ => raise "unreachable"%string
              end) ds' nil
        | LetK_e ks e =>
          ks' <- mapM (fun kxse => let '(k,xs,e) := kxse in
            e' <- contify_exp e ;;
            ret (k, xs, e')) ks ;;
          e' <- contify_exp e ;;
          ret (LetK_e ks' e')
      end).
    Defined.
  End monadic.

  Require Import ExtLib.Data.Monads.WriterMonad.
  Require Import ExtLib.Data.Monads.ReaderMonad.
  
  Definition contify (e : exp) : string + exp :=
    runReaderT (evalWriterT (Monoid_S := set_monoid) (evalWriterT (Monoid_S := map_monoid) (contify_exp e))) (Maps.empty : alist cont cont).

(*
  Module TESTS.
    Require Import ExtLib.Programming.Show.
    Require Import CoqCompile.CpsKConvert.
    Require Import CoqCompile.Parse.

(*
    Fixpoint even (x : nat) :=
      match x with
        | 0 => true
        | S n => odd n
      end
    with odd (x : nat) :=
      match x with
        | 0 => false
        | S n => even n
      end.
    Definition main := even 1.

    Extraction Language Scheme.
    Recursive Extraction main.
*)

    Definition even :=
      "(define even (lambda (x)
  (match x
     ((O) `(True))
     ((S n) (odd n)))))
  
(define odd (lambda (x)
  (match x
     ((O) `(False))
     ((S n) (even n)))))
  
(define main (even `(S ,`(O))))"%string.

    Definition simple :=
      "(define f (lambda (x) `(S ,x)))

       (define main (f `(S ,`(O))))"%string.

    Definition simple_no :=
      "(define f (lambda (x) `(S ,x)))

       (define main `(Pair ,f ,(f `(S ,`(O)))))"%string.
    
    Definition simple_lam := 
      Eval vm_compute in
      Parse.parse_topdecls simple.

    Definition simple_cps : CPSK.exp :=
      Eval vm_compute in
      match simple_lam as parsed return match parsed with
                                      | inl _ => unit
                                      | inr _ => CPSK.exp 
                                    end
        with
        | inl _ => tt
        | inr x => 
          let res := CpsKConvert.CPS_pure x in res (*
          match res with
            | Letrec_e (d :: nil) e => Let_e d e
            | _ => res
          end *)
      end.

    Eval vm_compute in to_string simple_cps.
    Eval vm_compute in to_string (contify simple_cps).


    Definition simple_no_lam := 
      Eval vm_compute in
      Parse.parse_topdecls simple_no.

    Definition simple_no_cps : CPSK.exp :=
      Eval vm_compute in
      match simple_no_lam as parsed return match parsed with
                                      | inl _ => unit
                                      | inr _ => CPSK.exp 
                                    end
        with
        | inl _ => tt
        | inr x => 
          let res := CpsKConvert.CPS_pure x in
          match res with
            | Letrec_e (d :: nil) e => Let_e d e
            | _ => res
          end
      end.

    Eval vm_compute in to_string simple_no_cps.
    Eval vm_compute in to_string (contify simple_no_cps).

    Definition even_lam := 
      Eval vm_compute in
      Parse.parse_topdecls even.

    Definition even_cps : CPSK.exp :=
      Eval vm_compute in
      match even_lam as parsed return match parsed with
                                      | inl _ => unit
                                      | inr _ => CPSK.exp 
                                    end
        with
        | inl _ => tt
        | inr x => 
          let res := CpsKConvert.CPS_pure x in res (*
          match res with
            | Letrec_e (d :: nil) e => Let_e d e
            | _ => res
          end *)
      end.

    Eval vm_compute in to_string even_cps.
    Eval vm_compute in to_string (contify even_cps).


  End TESTS.
*)    

End Contify.
