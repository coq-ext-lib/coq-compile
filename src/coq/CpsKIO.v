Require Import String List.
Require Import CoqCompile.CpsK.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Programming.Show.

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

(*
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
*)

  (** PrintChar :: ascii -> IO unit 
   ** fun k a => 
   **   let res = fun k' w =>
   **     let (x,w') = bind PrintChar (w::a::nil)
   **     in k' x w'
   **   in k res
   **)
  Definition IO_printChar (printchar : var) : decl :=
    let k := wrapCont "k" in
    let k' := wrapCont "k'" in
    let res := wrapVar "res" in
    let a := wrapVar "a" in
    let w := wrapVar "w" in
    let w' := wrapVar "w'" in
    let x := wrapVar "x" in
    let body :=
      Let_e (Bind_d x w' PrintChar_m ((Var_o w)::(Var_o a)::nil))
            (AppK_e k' (Var_o x :: Var_o w' :: nil))
    in
    Fn_d printchar (k :: nil) (a :: nil)
    (Let_e
      (Fn_d res (k' :: nil) (w :: nil) body)
      (AppK_e k (Var_o res :: nil))).

  (** Echo :: std -> ascii -> IO unit
   ** fun k s =>
   **   let res = 
   **     fun k a => 
   **       let res = fun k' w =>
   **         let (x,w') = bind PrintChar (w::a::nil)
   **         in k' x w'
   **       in k res
   **   in k res
   **)
  Definition IO_echo (echo : var) : decl :=
    let k := wrapCont "k" in
    let k' := wrapCont "k'" in
    let res := wrapVar "res" in
    let s := wrapVar "s" in
    let a := wrapVar "a" in
    let w := wrapVar "w" in
    let w' := wrapVar "w'" in
    let x := wrapVar "x" in
    let body :=
      (fix go (i : nat) (k : list op -> exp) : exp :=
        match i with
          | 0 => k nil
          | S i' =>
            let v := wrapVar ("a" ++ to_string i)%string in
            go i' (fun ops => 
              Let_e (Prim_d v Proj_p (Int_o (BinInt.Z.of_nat i) :: Var_o a :: nil))
                    (k (ops ++ Var_o v :: nil)))
        end) 8 (fun args =>
          Let_e (Bind_d x w' PrintChar_m (Var_o w :: Var_o s :: args))

                (AppK_e k' (Var_o x :: Var_o w' :: nil)))

    in
    Fn_d echo (k :: nil) (s :: nil)
      (Let_e
        (Fn_d res (k :: nil) (a :: nil)
          (Let_e
            (Fn_d res (k' :: nil) (w :: nil) body)
            (AppK_e k' (Var_o res :: nil))))
        (AppK_e k (Var_o res :: nil))).


  (** Read :: IO ascii
   ** fun k' w =>
   **   let (x,w') = bind Read (w::nil)
   **   in k' x w'
   **)
  Definition IO_read (read : var) : decl :=
    let k := wrapCont "k" in
    let w := wrapVar "w" in
    let w' := wrapVar "w'" in
    let x := wrapVar "x" in
    Fn_d read (k :: nil) (w :: nil) 
      (Let_e (Bind_d x w' Read_m (Var_o w :: nil))
             (AppK_e k (Var_o x :: Var_o w' :: nil))).
    
  Definition runIO (e : op) : exp :=
    let k := wrapCont "IO$k" in
    let w := wrapVar "IO$w" in
    let x := wrapVar "x" in
    let main := wrapVar "main" in 
    LetK_e ((k, x :: w :: nil, (Halt_e (Var_o x) (Var_o w)))::nil)
           (App_e e (k::nil) (InitWorld_o :: nil)).

  Definition wrapIO (bind ret printint printchar : var) (e : exp) : exp :=
    (* Let_e (IO_bind bind) (Let_e (IO_return ret) e). *)
    Let_e (IO_bind bind) (Let_e (IO_return ret) (Let_e (IO_printChar printchar) e)).

End IO.