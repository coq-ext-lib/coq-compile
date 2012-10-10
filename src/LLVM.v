Require Import Lambda Cps.
Require Import ZArith String List Bool.
Require Import ExtLib.Monad.Monad.
Require Import ExtLib.Monad.OptionMonad ExtLib.Monad.StateMonad.
Require Import ExtLib.Monad.Folds.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Decidables.Decidable.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

(** Provides abstract syntax and "ugly" printer for LLVM assembly code.
    I've tried to be relatively complete but there are a few missing
    instructions, attributes, etc. that we are very unlikely to use
    (e.g., things dealing with concurrency or intrinsics.)

    The ugly printer has not been tested at all. 

    We probably want to provide some some convenience on top of this
    for building abstract syntax that provides convenient defaults.
*)
Module LLVM.
  Import MonadNotation String.
  Local Open Scope string_scope.
  Local Open Scope monad_scope.
  Definition var := Lambda.var.
  Definition constructor := Lambda.constructor.
  Definition env_t := Lambda.env_t.
  Definition string_of_nat := LambdaNotation.nat2string.
  Definition string_of_Z := CPS.z2string.
  Definition label := string.

  Inductive cconv : Type := 
  | C_cc | Fast_cc | Cold_cc | CC10_cc | Num_cc : nat -> cconv.

  Definition double_quote := Ascii.ascii_of_nat 34.
  Definition quoted (s:string) := 
    String double_quote (s ++ (String double_quote EmptyString)).

  Definition string_of_cconv (c:cconv) : string := 
    quoted
    match c with 
      | C_cc => "ccc" | Fast_cc => "fastcc" | Cold_cc => "coldcc" | CC10_cc => "cc 10"
      | Num_cc n => "cc " ++ (string_of_nat n)
    end.

  Inductive linkage : Type := 
  | Private | Linker_private | Linker_private_weak | Linker_private_weak_def_auto 
  | Internal | Available_externally | Linkonce | Weak | Common | Appending | Extern_weak
  | Linkonce_odr | Weak_odr | External | Dllimport | Dllexport. 

  Definition string_of_linkage (l:linkage) : string := 
    match l with 
      | Private => "private"
      | Linker_private => "linker_private"
      | Linker_private_weak => "linker_private_weak"
      | Linker_private_weak_def_auto => "linker_private_weak_def_auto"
      | Internal => "internal"
      | Available_externally => "available_externally"
      | Linkonce => "linkonce"
      | Weak => "weak"
      | Common => "common"
      | Appending => "appending"
      | Extern_weak => "extern_weak"
      | Linkonce_odr => "linkonce_odr"
      | Weak_odr => "weak_odr"
      | External => "external"
      | Dllimport => "dllimport"
      | Dllexport => "dllexport"
    end.
      
  Inductive visibility : Type := | Default_v | Hidden_v | Protected_v.

  Definition string_of_visibility (v:visibility) : string := 
    quoted 
    match v with 
      | Default_v => "default" | Hidden_v => "hidden" | Protected_v => "protected"
    end.

  Inductive param_attr : Type := 
  | Zeroext_pattr | Signext_pattr | Inreg_pattr | Byval_pattr | Sret_pattr | Noalias_pattr
  | Nocapture_pattr | Nest_pattr.

  Definition string_of_param_attr (p:param_attr) : string := 
    match p with 
      | Zeroext_pattr => "zeroext" | Signext_pattr => "signext" | Inreg_pattr => "inreg" 
      | Byval_pattr => "byval" | Sret_pattr => "sret" | Noalias_pattr => "noalias"
      | Nocapture_pattr => "nocapture" | Nest_pattr => "nest"
    end.

  Inductive fn_attr : Type := 
  | Address_safety | Align_stack : nat -> fn_attr | Alwaysinline | Nonlazybind | Inlinehint
  | Naked | Noimplicitfloat | Noinline | Noredzone | Noreturn | Nounwind
  | Optsize | Readnone | Readonly | Returns_twice | Ssp | Sspreq | Uwtable.

  Definition string_of_fn_attr(f: fn_attr) : string := 
    match f with 
      | Address_safety => "address_safety" | Align_stack n => "alignstack(" ++ (string_of_nat n) ++ ")" 
      | Alwaysinline => "alwaysinline" | Nonlazybind => "nonlazybind" | Inlinehint => "inlinehint"
      | Naked => "naked" | Noimplicitfloat => "noimplicitfloat" | Noinline => "noinline" 
      | Noredzone => "noredzone" | Noreturn => "noreturn" | Nounwind => "nounwind"
      | Optsize => "optsize" | Readnone => "readnone" | Readonly => "readonly" 
      | Returns_twice => "returns_twice" | Ssp => "ssp" | Sspreq => "sspreq" | Uwtable => "uwtable"
    end.

  Inductive type : Type := 
  | I_t : nat -> type
  | Half_t | Float_t | Double_t | X86_fp80_t | Fp128_t | Ppc_fp128_t 
  | Void_t | Label_t | X86mmx_t | Metadata_t 
  | Array_t : list nat -> type -> type
  | Fn_t : forall (returntype: type) (arg_types : list type) (vararg : bool), type
  | Struct_t : forall (packed:bool) (elts : list type), type
  | Named_t : var -> type
  | Opaque_t : type
  | Pointer_t : forall (addrspace:nat), type -> type
  | Vector_t : nat -> type -> type.

  Fixpoint sep (s:string) (ss:list string) : string := 
    match ss with 
      | nil => ""
      | h::nil => h
      | h::t => h ++ s ++ (sep s t)
    end.

  Fixpoint string_of_type (t:type) : string := 
    match t with 
      | I_t n => "i" ++ (string_of_nat n)
      | Half_t => "half" | Float_t => "float" | Double_t => "double" | X86_fp80_t => "x86_fp80"
      | Fp128_t => "fp128" | Ppc_fp128_t => "ppc_fp128" | Void_t => "void" | Label_t => "label"
      | X86mmx_t => "x86mmx" | Metadata_t => "metadata"
      | Array_t ns t => 
        List.fold_right (fun (i:nat) (t:string) => 
                         "[" ++ (string_of_nat i) ++ " x " ++ t ++ "]") (string_of_type t) ns
      | Fn_t t ts vararg => 
        (string_of_type t) ++ "(" ++ (sep ", " (List.map string_of_type ts)) ++ 
        (if vararg then ",...)" else ")")
      | Struct_t packed elts => 
        let s := "{" ++ (sep ", " (List.map string_of_type elts)) ++ "}" in 
          if packed then "<" ++ s ++ ">" else s
      | Named_t x => x
      | Opaque_t => "opaque"
      | Pointer_t 0 t => (string_of_type t) ++ " *"
      | Pointer_t n t => (string_of_type t) ++ "addrspace(" ++ (string_of_nat n) ++ ") *"
      | Vector_t n t => "<" ++ (string_of_nat n) ++ " x " ++ (string_of_type t) ++ ">"
    end.

  Inductive constant : Type := 
  | True_c
  | False_c
  | Int_c : Z -> constant
  | Float_c : string -> constant
  | Null_c : constant
  | Global_c : var -> constant
  | Undef_c : constant
  | Zero_c : constant
  | Struct_c : list constant -> constant
  | Array_c : list constant -> constant
  | Vector_c : list constant -> constant
  | Metadata_c : list constant -> constant
  | Metastring_c : string -> constant.

  Fixpoint string_of_constant (c:constant) : string := 
    match c with 
      | True_c => "true" | False_c => "false" 
      | Int_c i => string_of_Z i
      | Float_c s => s | Null_c =>  "null" | Global_c v => v 
      | Undef_c => "undef" | Zero_c => "zeroinitializer"
      | Struct_c cs => "{" ++ (sep ", " (List.map string_of_constant cs)) ++ "}"
      | Array_c cs => "[" ++ (sep ", " (List.map string_of_constant cs)) ++ "]"
      | Vector_c cs => "<" ++ (sep ", " (List.map string_of_constant cs)) ++ ">"
      | Metastring_c s => "!" ++ (quoted s)
      | Metadata_c cs => "!{" ++ (sep ", " (List.map string_of_constant cs)) ++ "}"
    end.

  Inductive value : Type := 
  | Local : var -> value
  | Global : var -> value
  | AnonLocal : nat -> value
  | AnonGlobal : nat -> value
  | Constant : constant -> value.

  Definition string_of_value(v:value) : string := 
    match v with 
      | Local x => x
      | Global x => x
      | AnonLocal n => "%" ++ (string_of_nat n)
      | AnonGlobal n => "@" ++ (string_of_nat n)
      | Constant c => string_of_constant c
    end.

  Inductive cond : Type := 
  | Eq | Ne | Ugt | Uge | Ult | Ule | Sgt | Sge | Slt | Sle.

  Definition string_of_cond(c:cond) : string := 
    match c with 
      | Eq => "eq" | Ne => "ne" | Ugt => "ugt" | Uge => "uge" | Ult => "ult" | Ule => "ule" 
      | Sgt => "sgt" | Sge => "sge" | Slt => "slt" | Sle => "sle"
    end.

  Inductive fcond : Type := 
  | False_fc | Oeq_fc | Ogt_fc | Oge_fc | Olt_fc | Ole_fc | One_fc | Ord_fc | Ueq_fc
  | Ugt_fc | Uge_fc | Ult_fc | Ule_fc | Une_fc | Uno_fc | True_fc.

  Definition string_of_fcond(f:fcond) : string := 
    match f with 
      | False_fc => "false" | Oeq_fc => "oeq" | Ogt_fc => "ogt" | Oge_fc => "oge" | Olt_fc => "olt"
      | Ole_fc => "ole" | One_fc => "one" | Ord_fc => "ord" | Ueq_fc => "ueq" | Ugt_fc => "ugt"
      | Uge_fc => "uge" | Ult_fc => "ult" | Ule_fc => "ule" | Une_fc => "une" | Uno_fc => "uno"
      | True_fc => "true"
    end.

  Inductive exp : Type := 
  | Add_e : forall (nuw:bool) (nsw:bool) (ty:type) (op1:value) (op2:value), exp
  | Fadd_e : forall (ty:type) (op1:value) (op2:value), exp
  | Sub_e : forall (nuw:bool) (nsw:bool) (ty:type) (op1:value) (op2:value), exp
  | Fsub_e : forall (ty:type) (op1:value) (op2:value), exp
  | Mul_e : forall (nuw:bool) (nsw:bool) (ty:type) (op1:value) (op2:value), exp
  | Fmul_e : forall (ty:type) (op1:value) (op2:value), exp
  | Udiv_e : forall (exact:bool) (ty:type) (op1 op2:value), exp
  | Sdiv_e : forall (exact:bool) (ty:type) (op1 op2:value), exp
  | Fdiv_e : forall (ty:type) (op1:value) (op2:value), exp
  | Urem_e : forall (ty:type) (op1:value) (op2:value), exp
  | Srem_e : forall (ty:type) (op1:value) (op2:value), exp
  | Frem_e : forall (ty:type) (op1:value) (op2:value), exp
  | Shl_e : forall (nuw:bool) (nsw:bool) (ty:type) (op1:value) (op2:value), exp 
  | Lshr_e : forall (exact:bool) (ty:type) (op1 op2:value), exp
  | Ashr_e : forall (exact:bool) (ty:type) (op1 op2:value), exp
  | And_e : forall (ty:type) (op1 op2:value), exp
  | Or_e : forall (ty:type) (op1 op2:value), exp
  | Xor_e : forall (ty:type) (op1 op2:value), exp
  | Extractvalue_e : type -> value -> nat -> list nat -> exp
  | Insertvalue_e : type -> value -> type -> value -> nat -> list nat -> exp
  | Alloca_e : type -> option (type * nat) -> option nat -> exp
  | Load_e : forall (atomic:bool) (volatile:bool) (ty:type) (pointer:value) (align:option nat)
                    (nontemporal:option nat) (invariant:option nat) (singlethread:bool), exp
  | Getelementptr_e : forall (inbounds:bool)(pointer_ty:type) (pointerval: value), list (type * value) -> exp
  | Trunc_e : type -> value -> type -> exp
  | Zext_e : type -> value -> type -> exp
  | Sext_e : type -> value -> type -> exp
  | Fptrunc_e : type -> value -> type -> exp
  | Fpext_e : type -> value -> type -> exp
  | Fptoui_e : type -> value -> type -> exp
  | Fptosi_e : type -> value -> type -> exp
  | Uitofp_e : type -> value -> type -> exp
  | Sitofp_e : type -> value -> type -> exp
  | Ptrtoint_e : type -> value -> type -> exp
  | Inttoptr_e : type -> value -> type -> exp
  | Bitcast_e : type -> value -> type -> exp
  | Icmp_e : cond -> type -> value -> value -> exp
  | Fcmp_e : fcond -> type -> value -> value -> exp
  | Phi_e : type -> list (value * label) -> exp
  | Select_e : type -> value -> type -> value -> type -> value -> exp
  | Call_e : forall (tail:bool) (convention: option cconv) (ret_attrs:list param_attr) (ty:type) 
                    (fnptrty: option type) (fnptr:value) 
                    (args : list (type * value * (list param_attr))) 
                    (fn_attrs: list fn_attr), exp.

  Definition flag(b:bool)(s:string) : string := if b then s else "".

  Definition string_of_arith(opcode:string)(nuw nsw:bool)(ty:type)(op1 op2:value) : string := 
    opcode ++ " " ++ (flag nuw "nuw ") ++ (flag nsw "nsw ") ++ (string_of_type ty) ++ " " ++ 
    (string_of_value op1) ++ ", " ++ (string_of_value op2).

  Definition string_of_binop(opcode:string)(ty:type)(op1 op2:value) := 
    string_of_arith opcode false false ty op1 op2.

  Definition string_of_logical(opcode:string)(ex:bool)(ty:type)(op1 op2:value) : string := 
    opcode ++ " " ++ (flag ex "exact ") ++ (string_of_type ty) ++ " " ++ (string_of_value op1)
    ++ ", " ++ (string_of_value op2).

  Definition string_of_conv(opcode:string)(ty1:type)(op:value)(ty2:type) : string := 
    opcode ++ " " ++ (string_of_type ty1) ++ " " ++ (string_of_value op) ++ " to " ++ (string_of_type ty2).

  Definition string_of_option{A:Type}(f:A -> string)(x:option A):string := 
    match x with 
      | None => ""
      | Some v => f v
    end.

  Definition string_of_exp(e:exp) : string := 
    match e with 
      | Add_e nuw nsw ty op1 op2 => string_of_arith "add" nuw nsw ty op1 op2
      | Fadd_e ty op1 op2 => string_of_binop "fadd" ty op1 op2
      | Sub_e nuw nsw ty op1 op2 => string_of_arith "sub" nuw nsw ty op1 op2
      | Fsub_e ty op1 op2 => string_of_binop "fsub" ty op1 op2
      | Mul_e nuw nsw ty op1 op2 => string_of_arith "mul" nuw nsw ty op1 op2
      | Fmul_e ty op1 op2 => string_of_binop "fmul" ty op1 op2
      | Udiv_e ex ty op1 op2 => string_of_logical "udiv" ex ty op1 op2
      | Sdiv_e ex ty op1 op2 => string_of_logical "sdiv" ex ty op1 op2
      | Fdiv_e ty op1 op2 => string_of_binop "fdiv" ty op1 op2
      | Urem_e ty op1 op2 => string_of_binop "urem" ty op1 op2
      | Srem_e ty op1 op2 => string_of_binop "srem" ty op1 op2
      | Frem_e ty op1 op2 => string_of_binop "frem" ty op1 op2
      | Shl_e nuw nsw ty op1 op2 => string_of_arith "shl" nuw nsw ty op1 op2
      | Lshr_e ex ty op1 op2 => string_of_logical "lshr" ex ty op1 op2
      | Ashr_e ex ty op1 op2 => string_of_logical "ashr" ex ty op1 op2
      | And_e ty op1 op2 => string_of_binop "and" ty op1 op2
      | Or_e ty op1 op2 => string_of_binop "or" ty op1 op2
      | Xor_e ty op1 op2 => string_of_binop "xor" ty op1 op2
      | Extractvalue_e ty op n ns => 
        "extractvalue " ++ (string_of_type ty) ++ " " ++ (string_of_value op) ++ ", " ++
        (sep ", " (List.map string_of_nat (n::ns)))
      | Insertvalue_e ty1 op1 ty2 op2 n ns =>
        "insertvalue " ++ (string_of_type ty1) ++ " " ++ (string_of_value op1) ++ ", " ++
        (string_of_type ty2) ++ " " ++ (string_of_value op2) ++ ", " ++
        (sep ", " (List.map string_of_nat (n::ns)))
      | Alloca_e ty opttynum optalign => 
        "alloca " ++ (string_of_type ty) ++ 
        (match opttynum with None => "" 
           | Some (ty,n) => ", " ++ (string_of_type ty) ++ " " ++ (string_of_nat n) end) ++
        (match optalign with None => "" | Some n => ", align " ++ (string_of_nat n) end)
      | Load_e atomic volatile ty pointer align nontemporal invariant singlethread => 
        (* fixme: just doing the simple stuff here *)
        "load " ++ (flag atomic "atomic ") ++ (flag volatile "volatile ") ++ 
        (string_of_type ty) ++ " " ++ (string_of_value pointer) ++ " " ++ (flag singlethread "singlethread ")
        ++ (match align with None => "" | Some n => ", align " ++ (string_of_nat n) end)
      | Getelementptr_e inbounds ty v indexes =>
        "getelementptr " ++ (flag inbounds "inbounds ") ++ (string_of_type ty) ++ " " ++ 
        (sep ", " ((string_of_value v)::
          (List.map (fun p => (string_of_type (fst p)) ++ " " ++ (string_of_value (snd p))) indexes)))
      | Trunc_e ty1 v ty2 => string_of_conv "trunc" ty1 v ty2 
      | Zext_e ty1 v ty2 => string_of_conv "zext" ty1 v ty2 
      | Sext_e ty1 v ty2 => string_of_conv "sext" ty1 v ty2 
      | Fptrunc_e ty1 v ty2 => string_of_conv "fptrunc" ty1 v ty2 
      | Fpext_e ty1 v ty2 => string_of_conv "fpext" ty1 v ty2 
      | Fptoui_e ty1 v ty2 => string_of_conv "fptoui" ty1 v ty2 
      | Fptosi_e ty1 v ty2 => string_of_conv "fptosi" ty1 v ty2 
      | Uitofp_e ty1 v ty2 => string_of_conv "uitofp" ty1 v ty2 
      | Sitofp_e ty1 v ty2 => string_of_conv "sitofp" ty1 v ty2 
      | Ptrtoint_e ty1 v ty2 => string_of_conv "ptrtoint" ty1 v ty2 
      | Inttoptr_e ty1 v ty2 => string_of_conv "inttoptr" ty1 v ty2 
      | Bitcast_e ty1 v ty2 => string_of_conv "bitcast" ty1 v ty2 
      | Icmp_e cond ty v1 v2 => "icmp " ++ (string_of_cond cond) ++ " " ++ (string_of_type ty) ++
        (string_of_value v1) ++ ", " ++ (string_of_value v2)
      | Fcmp_e cond ty v1 v2 => "fcmp " ++ (string_of_fcond cond) ++ " " ++ (string_of_type ty) ++
        (string_of_value v1) ++ ", " ++ (string_of_value v2)
      | Phi_e ty vls => 
        "phi " ++ (string_of_type ty) ++ " " ++ 
        (sep ", " (List.map (fun p => "[ " ++ (string_of_value (fst p)) ++ ", " ++ (snd p) ++ " ]") vls))
      | Select_e ty1 v1 ty2 v2 ty3 v3 => 
        "select " ++ (string_of_type ty1) ++ " " ++ (string_of_value v1) ++ ", " ++ 
        (string_of_type ty2) ++ " " ++ (string_of_value v2) ++ ", " ++ 
        (string_of_type ty3) ++ " " ++ (string_of_value v3)
      | Call_e tail conv ret_attrs ty fnptrty fnptr args fnattrs =>
        (flag tail "tail ") ++ "call " ++ (string_of_option string_of_cconv conv) ++ " " ++
        (sep " " (List.map string_of_param_attr ret_attrs)) ++ " " ++
        (string_of_type ty) ++ " " ++ (string_of_option string_of_type fnptrty) ++ 
        (string_of_value fnptr) ++ "(" ++
        (sep ", " (List.map (fun x => match x with | (t,v,a) => 
                                        (string_of_type t) ++ " " ++ (string_of_value v) ++ 
                                        (sep " " (List.map string_of_param_attr a))
                                      end) args)) 
        ++ ") " ++ (sep " " (List.map string_of_fn_attr fnattrs))
    end.
  
  Inductive instr : Type := 
  | Comment_i : string -> instr
  | Ret_i : option (type * value) -> instr
  | Br_cond_i : value -> label -> label -> instr
  | Br_uncond_i : label -> instr
  | Switch_i : type -> value -> label -> list (type * Z * label) -> instr
  | Resume_i : type -> value -> instr
  | Unreachable_i : instr
  | Assign_i : (option value) -> exp -> instr
  | Store_i : forall (atomic:bool) (volatile:bool) (ty:type) (v:value) (ptrty:type) (pointer:value) 
                     (align:option nat) (nontemporal:option nat) (singlethread:bool), instr.

  Definition string_of_instr(i:instr) : string := 
    match i with 
      | Comment_i s => "; " ++ s
      | Ret_i vopt => 
          "ret " ++ 
          (string_of_option (fun p => (string_of_type (fst p) ++ " " ++ (string_of_value (snd p)))) vopt)
      | Br_cond_i v l1 l2 => 
          "br i1 " ++ (string_of_value v) ++ " label " ++ l1 ++ ", label " ++ l2
      | Br_uncond_i l => 
          "br label "++l
      | Switch_i t v def arms => 
          "switch " ++ (string_of_type t) ++ " " ++ (string_of_value v) ++ ", label " ++ def ++ " [" ++
          (sep " " (List.map (fun p => match p with | (t,i,l) => 
                                         (string_of_type t) ++ " " ++ (string_of_Z i) ++ ", label " ++ l
                                       end) arms)) ++ " ]"
      | Resume_i t v => 
          "resume " ++ (string_of_type t) ++ " " ++ (string_of_value v)
      | Unreachable_i => "unreachable"
      | Assign_i (Some x) e => (string_of_value x) ++ " = " ++ (string_of_exp e)
      | Assign_i None e => (string_of_exp e)
      | Store_i atomic volatile ty v ptrty pointer align nontemporal singlethread => 
        (* fix -- doesn't do nontemporal or ordering *)
        "store " ++ (flag atomic "atomic ") ++ (flag volatile "volatile ") ++ (string_of_type ty) ++ " " ++
        (string_of_value v) ++ ", " ++ (string_of_type ptrty) ++ " " ++ (string_of_value pointer) ++ " " ++
        (flag singlethread "singlethread ") ++ 
        (string_of_option (fun n => ", align "++(string_of_nat n)++" ") align)
    end.

  Definition ST := state (list string).
  Definition emit : string -> ST unit := CPS.emit.
  Definition spaces (n:nat) : ST unit := emit (CPS.spaces n).
  Definition newline : ST unit := emit CPS.newline.
  Definition iter := @CPS.iter.
  Definition emit_option {A} (f:A -> ST unit) (x:option A) : ST unit := 
    match x with 
      | None => ret tt
      | Some v => f v 
    end.
  Definition emit_option_s {A} (f:A -> ST unit) (x:option A) : ST unit := 
    match x with 
      | None => ret tt
      | Some v => f v ;; emit " "
    end.

  Definition emit_instr (i:instr) : state (list string) unit := 
    spaces 4 ;; emit (string_of_instr i) ;; newline.

  Definition block := ((option label) * (list instr))%type.

  Definition emit_block (b:block) : state (list string) unit := 
    emit_option (fun l => spaces 2 ;; emit l ;; emit ":" ;; newline) (fst b) ;; 
    iter emit_instr (snd b).

  Definition pipe {A B C} (f:B -> C) (g:A -> B) : A -> C := 
    fun x => f (g x).

  Infix "$" := pipe (at level 70, right associativity).

  Record fn_header : Type := {
    linkage_fh : option linkage ; 
    visibility_fh : option visibility ; 
    cconv_fh : option cconv ; 
    unnamed_addr_fh : bool ; 
    return_type_fh : type ; 
    return_type_attrs_fh : list param_attr ; 
    name_fh : var ; 
    args_fh : list (type * var * list (param_attr)) ; 
    attrs_fh : list fn_attr ; 
    section_fh : option string ; 
    align_fh : option nat ; 
    gc_fh : option string
  }.

  Definition emit_fn_header (drop_vars:bool) (fh:fn_header) : state (list string) unit := 
    emit_option_s (emit $ string_of_linkage) (linkage_fh fh) ;; 
    emit_option_s (emit $ string_of_visibility) (visibility_fh fh) ;; 
    emit_option_s (emit $ string_of_cconv) (cconv_fh fh) ;;
    (if (unnamed_addr_fh fh) then emit "unnamed_addr " else ret tt) ;; 
    emit (string_of_type (return_type_fh fh)) ;; emit " " ;;
    iter (fun x => emit (string_of_param_attr x) ;; emit " ") (return_type_attrs_fh fh) ;;
    emit (name_fh fh) ;; emit "(" ;; 
    iter (fun p => match p with (t,x,attrs) => 
                     emit (string_of_type t) ;; 
                     (if drop_vars then ret tt else emit x) ;;
                     iter (fun x => emit (string_of_param_attr x) ;; emit " ") attrs
                   end) (args_fh fh) ;;
    emit ") " ;;
    iter (fun x => emit (string_of_fn_attr x) ;; emit " ") (attrs_fh fh) ;;
    emit_option_s (fun s => emit ", section " ;; emit (quoted s) ;; emit " ") (section_fh fh) ;;
    emit_option_s (fun n => emit ", align " ;; emit (string_of_nat n) ;; emit " ") (align_fh fh) ;;
    emit_option_s (fun s => emit "gc " ;; emit (quoted s) ;; emit " ") (gc_fh fh).
    
  Inductive topdecl : Type := 
  | Global_d : forall (x:var) (addrspace:option nat) (l:option linkage) (unnamed_addr:bool) (const:bool) 
                      (t:type) (c:constant) (section:option string) (align:option nat), topdecl
  | Define_d : fn_header -> list block -> topdecl
  | Declare_d : fn_header -> topdecl
  | Alias_d : forall (x:var) (l:option linkage) (v:option visibility) (t:type) (e:exp), topdecl
  | Metadata_d : forall (x:var), list constant -> topdecl.

  Definition emit_topdecl (t:topdecl) : ST unit := 
    match t with 
      | Global_d x a l u c t v s al => 
        emit x ;; emit " = " ;;
        emit_option_s (fun n => emit "addrspace(" ;; emit (string_of_nat n) ;; emit ")") a ;;
        emit_option_s (emit $ string_of_linkage) l ;;
        (if u then emit "unnamed_addr " else ret tt) ;;
        (if c then emit "constant " else ret tt) ;;
        emit (string_of_type t) ;; emit " " ;; 
        emit (string_of_constant v) ;; emit " " ;;
        emit_option_s (fun s => emit ", section " ;; emit (quoted s) ;; emit " ") s ;;
        emit_option_s (fun n => emit ", align " ;; emit (string_of_nat n) ;; emit " ") al ;;
        newline 
      | Define_d fh bs => 
        emit_fn_header true fh ;; emit " {" ;; newline ;; iter emit_block bs ;; emit "}" ;; newline
      | Declare_d fh => emit_fn_header false fh ;; newline
      | Alias_d x l v t e => 
        emit x ;; emit " = alias " ;; 
        emit_option_s (emit $ string_of_linkage) l ;;
        emit_option_s (emit $ string_of_visibility) v ;;
        emit (string_of_type t) ;; emit " " ;; 
        emit (string_of_exp e) ;; newline
      | Metadata_d x cs => 
        emit x ;; emit " = metadata !{" ;; emit (sep ", " (List.map string_of_constant cs)) ;; 
        emit "}" ;; newline
    end.

  Definition module := list topdecl.

  Definition emit_module (m:module) : ST unit := iter emit_topdecl m.

  Definition runST (c:ST unit) := 
    List.fold_left (fun x y => x ++ y) (snd (runState c nil)).

  Definition string_of_module := runST $ emit_module.
  Definition string_of_topdecl := runST $ emit_topdecl.
  Definition string_of_fn_header b := runST $ (emit_fn_header b).
      
End LLVM.
