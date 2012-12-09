Require Import CoqCompile.Cps CoqCompile.CpsK.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Lists.

(** Converting from CpsK to Cps requires that we convert
 ** all of the second-class continuations into first-class
 ** functions
 **)

Definition cont2var (c : CPSK.cont) : Env.var :=
  match c with
    | CPSK.K n p => Env.mkVar (Some n) p
  end.

Fixpoint cpsk2cps_exp (e : CPSK.exp) : CPS.exp :=
  match e with
    | CPSK.App_e o ks os =>
      CPS.App_e o ((map (fun x => CpsCommon.Var_o (cont2var x)) ks) ++ os)
    | CPSK.Let_e d e => 
      CPS.Let_e (cpsk2cps_decl d) (cpsk2cps_exp e)
    | CPSK.Letrec_e ds e =>
      CPS.Letrec_e (map cpsk2cps_decl ds) (cpsk2cps_exp e)
    | CPSK.Switch_e o ps d =>
      let ps := map (fun p_e => let '(p,e) := p_e in
        (p, cpsk2cps_exp e)) ps in
      let d := map cpsk2cps_exp d in
      CPS.Switch_e o ps d        
    | CPSK.Halt_e o o' =>
      CPS.Halt_e o o'

    | CPSK.AppK_e k os =>
      CPS.App_e (CpsCommon.Var_o (cont2var k)) os
    | CPSK.LetK_e ks e =>
      CPS.Letrec_e 
      (map (fun k_args_body => let '(k,args,body) := k_args_body in
              CPS.Fn_d (cont2var k) args (cpsk2cps_exp body)) ks)
      (cpsk2cps_exp e)
  end
with cpsk2cps_decl (d : CPSK.decl) : CPS.decl :=
  match d with
    | CPSK.Op_d v o => CPS.Op_d v o
    | CPSK.Prim_d v p os => CPS.Prim_d v p os
    | CPSK.Bind_d v w p os => CPS.Bind_d v w p os
    | CPSK.Fn_d v ks args body => CPS.Fn_d v args (cpsk2cps_exp body)      
  end.
