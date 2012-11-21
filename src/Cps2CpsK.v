Require Import CoqCompile.Cps CoqCompile.CpsK.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Lists.

(** There are several translations from Cps to CpsK.
 ** The simplest just uses nil as all the continuations
 **)

Fixpoint cps2cpsk_exp (e : CPS.exp) : CPSK.exp :=
  match e with
    | CPS.App_e o os =>
      CPSK.App_e o nil os
    | CPS.Let_e d e => 
      CPSK.Let_e (cps2cpsk_decl d) (cps2cpsk_exp e)
    | CPS.Letrec_e ds e =>
      CPSK.Letrec_e (map cps2cpsk_decl ds) (cps2cpsk_exp e)
    | CPS.Switch_e o ps d =>
      let ps := map (fun p_e => let '(p,e) := p_e in
        (p, cps2cpsk_exp e)) ps in
      let d := map cps2cpsk_exp d in
      CPSK.Switch_e o ps d        
    | CPS.Halt_e o o' =>
      CPSK.Halt_e o o'
  end
with cps2cpsk_decl (d : CPS.decl) : CPSK.decl :=
  match d with
    | CPS.Op_d v o => CPSK.Op_d v o
    | CPS.Prim_d v p os => CPSK.Prim_d v p os
    | CPS.Bind_d v w p os => CPSK.Bind_d v w p os
    | CPS.Fn_d v args body => CPSK.Fn_d v nil args (cps2cpsk_exp body)      
  end.