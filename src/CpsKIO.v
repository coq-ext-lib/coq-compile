Require Import List.
Require Import CoqCompile.CpsK.
Require Import ExtLib.Core.RelDec.

Module IO.
  Import CPSK.

  (** Note:
   ** IO t = (t -> world -> _|_) -> world -> _|_
   **)

  (** Return :: t -> IO t
   ** fun k x =>
   **   let res = fun k' w => k' x w
   **   in k res
   **)
  Definition IO_return (ret : var) : decl :=
    let k := wrapCont "k" in
    let k' := wrapCont "k'" in
    let x := wrapVar "x" in 
    let res := wrapVar "res" in
    let w := wrapVar "w" in
    Fn_d ret (k :: nil) (x :: nil)
      (Let_e 
        (Fn_d res (k'::nil) (w :: nil) (AppK_e k' (Var_o x :: Var_o w :: nil)))
        (AppK_e k (Var_o res :: nil))).

  (** Bind :: IO t -> (t -> IO u) -> IO u
   ** fun k c =>
   **   let res = fun k' f =>
   **     let res = fun k'' w => 
   **       let k = fun x w => 
   **         let k' = fun c => c k'' w in
   **         f k' x
   **       in c k w
   **     in k' res
   **   in k res
   **)
  Definition IO_bind (bind : var) : decl :=
    let k := wrapCont "k" in
    let k' := wrapCont "k'" in
    let k'' := wrapCont "k''" in
    let c := wrapVar "c" in
    let res := wrapVar "res" in
    let f := wrapVar "f" in
    let w := wrapVar "w" in
    let x := wrapVar "x" in
    Fn_d bind (k::nil) (c :: nil) 
    (Let_e 
      (Fn_d res (k'::nil) (f :: nil) 
        (Let_e
          (Fn_d res (k''::nil) (w :: nil) 
            (LetK_e ((k, x :: w :: nil, 
                (LetK_e ((k', c :: nil, (App_e (Var_o c) (k''::nil) (Var_o w :: nil))) :: nil)
                  (App_e (Var_o f) (k'::nil) (Var_o x :: nil)))
              )::nil)
              (App_e (Var_o c) (k::nil) (Var_o w :: nil))))
          (AppK_e k' (Var_o res :: nil))
        )
      )
      (AppK_e k (Var_o res :: nil))).

  (** PrintIO :: Z -> IO unit
   ** fun k i =>
   **   let res = fun k' w =>
   **     let (x, w') = bind PrintInt (w :: i :: nil) in
   **     k' x w'
   **   in k res
   **)
  Definition IO_printInt (printint : var) : decl :=
    let k := wrapCont "k" in
    let k' := wrapCont "k'" in
    let res := wrapVar "res" in
    let i := wrapVar "i" in
    let w := wrapVar "w" in
    let w' := wrapVar "w'" in
    let x := wrapVar "x" in
    Fn_d printint (k :: nil) (i :: nil)
    (Let_e
      (Fn_d res (k' :: nil) (w :: nil)
        (Let_e
          (Bind_d x w' PrintInt_m (Var_o w :: Var_o i :: nil))
          (AppK_e k' (Var_o x :: Var_o w' :: nil))))
      (AppK_e k (Var_o res :: nil))).
    
  Definition runIO (e : op) : exp :=
    let k := wrapCont "IO$k" in
    let w := wrapVar "IO$w" in
    let x := wrapVar "x" in
    let main := wrapVar "main" in 
    LetK_e ((k, x :: w :: nil, (Halt_e (Var_o x) (Var_o w)))::nil)
           (App_e e (k::nil) (InitWorld_o :: nil)).

  Definition wrapIO (bind ret printint : var) (e : exp) : exp :=
     Let_e (IO_bind bind) (Let_e (IO_return ret) (Let_e (IO_printInt printint) e)).

End IO.