Require Import List.
Require Import CoqCompile.Cps.
Require Import ExtLib.Core.RelDec.

Module IO.
  Import CPS.

  (** Note:
   ** IO t = (t -> world -> _|_) -> world -> _|_
   **)

  (** Return :: t -> IO t
   ** fun k x =>
   **   let res = fun k' w => k' x w
   **   in k res
   **)
  Definition IO_return (ret : var) : decl :=
    let k := wrapVar "k" in
    let x := wrapVar "x" in 
    let res := wrapVar "res" in
    let k' := wrapVar "k'" in
    let w := wrapVar "w" in
    Fn_d ret (k :: x :: nil)
      (Let_e 
        (Fn_d res (k' :: w :: nil) (App_e (Var_o k') (Var_o x :: Var_o w :: nil)))
        (App_e (Var_o k) (Var_o res :: nil))).

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
    let k := wrapVar "k" in
    let c := wrapVar "c" in
    let res := wrapVar "res" in
    let k' := wrapVar "k'" in
    let k'' := wrapVar "k''" in
    let f := wrapVar "f" in
    let w := wrapVar "w" in
    let x := wrapVar "x" in
    Fn_d bind (k :: c :: nil) 
    (Let_e 
      (Fn_d res (k' :: f :: nil) 
        (Let_e
          (Fn_d res (k'' :: w :: nil) 
            (Let_e 
              (Fn_d k (x :: w :: nil) 
                (Let_e
                  (Fn_d k' (c :: nil) (App_e (Var_o c) (Var_o k'' :: Var_o w :: nil)))
                  (App_e (Var_o f) (Var_o k' :: Var_o x :: nil)))
              )
              (App_e (Var_o c) (Var_o k :: Var_o w :: nil))))
          (App_e (Var_o k') (Var_o res :: nil))
        )
      )
      (App_e (Var_o k) (Var_o res :: nil))).

  Definition runIO (e : op) : exp :=
    let k :=
      let k := wrapVar "IO$k" in
      if eq_dec (Var_o k) e then 
        wrapVar "IO$k'"
      else
        k
    in
    let w := wrapVar "IO$w" in
    let x := wrapVar "x" in
    let main := wrapVar "main" in 
    Let_e (Fn_d k (x :: w :: nil) (Halt_e (Var_o x) (Var_o w)))
          (App_e e (InitWorld_o :: Var_o k :: nil)).

  Definition wrapIO (bind ret : var) (e : exp) : exp :=
     Let_e (IO_bind bind) (Let_e (IO_return ret) e).

End IO.