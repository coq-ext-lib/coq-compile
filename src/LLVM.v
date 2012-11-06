Require Import Lambda Cps.
Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Folds.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Data.Char.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Core.RelDec.
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
  Definition constructor := Lambda.constructor.
  Definition var := string.
  Definition env_t := Lambda.env_t.
  Definition label := string.

  Inductive cconv : Type := 
  | X86_fastcallcc | C_cc | Fast_cc | Cold_cc | CC10_cc | Num_cc : nat -> cconv.

  Definition double_quote := Ascii.ascii_of_nat 34.
  Definition quoted (s:string) := 
    String double_quote (s ++ (String double_quote EmptyString)).

  Inductive linkage : Type := 
  | Private | Linker_private | Linker_private_weak | Linker_private_weak_def_auto 
  | Internal | Available_externally | Linkonce | Weak | Common | Appending | Extern_weak
  | Linkonce_odr | Weak_odr | External | Dllimport | Dllexport. 
      
  Inductive visibility : Type := | Default_v | Hidden_v | Protected_v.

  Inductive param_attr : Type := 
  | Zeroext_pattr | Signext_pattr | Inreg_pattr | Byval_pattr | Sret_pattr | Noalias_pattr
  | Nocapture_pattr | Nest_pattr.


  Inductive fn_attr : Type := 
  | Address_safety | Align_stack : nat -> fn_attr | Alwaysinline | Nonlazybind | Inlinehint
  | Naked | Noimplicitfloat | Noinline | Noredzone | Noreturn | Nounwind
  | Optsize | Readnone | Readonly | Returns_twice | Ssp | Sspreq | Uwtable.


  Inductive type : Type := 
  | I_t : nat -> type
  | Half_t | Float_t | Double_t | X86_fp80_t | Fp128_t | Ppc_fp128_t 
  | Void_t | Label_t | X86mmx_t | Metadata_t 
  | Array_t : list nat -> type -> type
  | Fn_t : forall (returntype: type) (arg_types : list type) (vararg : bool), type
  | Struct_t : forall (packed:bool) (elts : list type), type
  | Named_t : string -> type
  | Opaque_t : type
  | Pointer_t : forall (addrspace:nat), type -> type
  | Vector_t : nat -> type -> type.

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

  Inductive value : Type := 
  | Local : var -> value
  | Global : var -> value
  | AnonLocal : nat -> value
  | AnonGlobal : nat -> value
  | Constant : constant -> value.

  Inductive cond : Type := 
  | Eq | Ne | Ugt | Uge | Ult | Ule | Sgt | Sge | Slt | Sle.

  Inductive fcond : Type := 
  | False_fc | Oeq_fc | Ogt_fc | Oge_fc | Olt_fc | Ole_fc | One_fc | Ord_fc | Ueq_fc
  | Ugt_fc | Uge_fc | Ult_fc | Ule_fc | Une_fc | Uno_fc | True_fc.

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

  Definition block := ((option label) * (list instr))%type.
    
  Inductive topdecl : Type := 
  | Global_d : forall (x:var) (addrspace:option nat) (l:option linkage) (unnamed_addr:bool) (const:bool) 
                      (t:type) (c:constant) (section:option string) (align:option nat), topdecl
  | Define_d : fn_header -> list block -> topdecl
  | Declare_d : fn_header -> topdecl
  | Alias_d : forall (x:var) (l:option linkage) (v:option visibility) (t:type) (e:exp), topdecl
  | Metadata_d : forall (x:var), list constant -> topdecl.

  Definition module := list topdecl.

  Section Printing.
    Require Import ExtLib.Programming.Show.
    Import ShowNotation.
    Local Open Scope show_scope.

    Global Instance Show_cconv : Show cconv :=
      fun c => 
        match c with 
          | X86_fastcallcc => "x86_fastcallcc" 
          | C_cc => "ccc" | Fast_cc => "fastcc" | Cold_cc => "coldcc" | CC10_cc => "cc 10"
          | Num_cc n => "cc " << show n 
        end.

    Global Instance Show_linkage : Show linkage :=
      fun l => 
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

    Global Instance Show_param_attr : Show param_attr :=
      fun p => 
        match p with 
          | Zeroext_pattr => "zeroext" | Signext_pattr => "signext" | Inreg_pattr => "inreg" 
          | Byval_pattr => "byval" | Sret_pattr => "sret" | Noalias_pattr => "noalias"
          | Nocapture_pattr => "nocapture" | Nest_pattr => "nest"
        end.

    Global Instance Show_visibility : Show visibility :=
      fun v => quoted 
        match v with 
          | Default_v => "default" | Hidden_v => "hidden" | Protected_v => "protected"
        end.

    Global Instance Show_fn_attr : Show fn_attr :=
      fun f =>
        match f with 
          | Address_safety => "address_safety" 
          | Align_stack n => "alignstack(" << show n << ")" 
          | Alwaysinline => "alwaysinline" 
          | Nonlazybind => "nonlazybind"
          | Inlinehint => "inlinehint"
          | Naked => "naked"
          | Noimplicitfloat => "noimplicitfloat"
          | Noinline => "noinline" 
          | Noredzone => "noredzone"
          | Noreturn => "noreturn"
          | Nounwind => "nounwind"
          | Optsize => "optsize"
          | Readnone => "readnone"
          | Readonly => "readonly" 
          | Returns_twice => "returns_twice"
          | Ssp => "ssp"
          | Sspreq => "sspreq"
          | Uwtable => "uwtable"
        end.

    Global Instance Show_type : Show type :=
      fix show_type (t : type) : showM :=
        match t with 
          | I_t n => "i" << show n
          | Half_t => "half"
          | Float_t => "float"
          | Double_t => "double"
          | X86_fp80_t => "x86_fp80"
          | Fp128_t => "fp128"
          | Ppc_fp128_t => "ppc_fp128"
          | Void_t => "void"
          | Label_t => "label"
          | X86mmx_t => "x86mmx"
          | Metadata_t => "metadata"
          | Array_t ns t => 
            List.fold_right (fun (i:nat) (t:showM) => 
                         "[" << show i << " x " << t << "]") (show_type t) ns
          | Fn_t t ts vararg => 
            show_type t << "(" << sepBy ", " (List.map show_type ts) << 
            (if vararg then ",...)" else ")")
          | Struct_t packed elts => 
            let s := "{" << (sepBy ", " (List.map show_type elts)) << "}" in 
            if packed then "<" << s << ">" else s
          | Named_t x => x
          | Opaque_t => "opaque"
          | Pointer_t 0 t => show_type t << " *"
          | Pointer_t n t => show_type t << "addrspace(" << show n << ") *"
          | Vector_t n t => "<" << show n << " x " << show_type t << ">"
        end.
    
    Global Instance Show_constant : Show constant :=
      fix show_constant c := 
        match c return showM with 
          | True_c => "true" 
          | False_c => "false" 
          | Int_c i => show i
          | Float_c s => s
          | Null_c =>  "null"
          | Global_c v => v 
          | Undef_c => "undef"
          | Zero_c => "zeroinitializer"
          | Struct_c cs => "{" << sepBy ", " (List.map show_constant cs) << "}"
          | Array_c cs => "[" << sepBy ", " (List.map show_constant cs) << "]"
          | Vector_c cs => "<" << sepBy ", " (List.map show_constant cs) << ">"
          | Metastring_c s => "!" << (quoted s)
          | Metadata_c cs => "!{" << sepBy ", " (List.map show_constant cs) << "}"
        end.
    
    Global Instance Show_value : Show value :=
      fun v =>
        match v with 
          | Local x => "%" << x
          | Global x => "@" << x
          | AnonLocal n => "%" << show n
          | AnonGlobal n => "@" << show n
          | Constant c => show c
        end.

    Global Instance Show_cond : Show cond :=
      fun c =>
        match c with 
          | Eq => "eq" | Ne => "ne" | Ugt => "ugt" | Uge => "uge" | Ult => "ult" | Ule => "ule" 
          | Sgt => "sgt" | Sge => "sge" | Slt => "slt" | Sle => "sle"
        end.

    Global Instance Show_fcond : Show fcond :=
      fun f =>
        match f with 
          | False_fc => "false" | Oeq_fc => "oeq" | Ogt_fc => "ogt" | Oge_fc => "oge" | Olt_fc => "olt"
          | Ole_fc => "ole" | One_fc => "one" | Ord_fc => "ord" | Ueq_fc => "ueq" | Ugt_fc => "ugt"
          | Uge_fc => "uge" | Ult_fc => "ult" | Ule_fc => "ule" | Une_fc => "une" | Uno_fc => "uno"
          | True_fc => "true"
        end.

    Definition option_show (T : Type) (f : T -> showM) (o : option T) : showM :=
      match o with
        | None => empty
        | Some x => f x 
      end.
    
    Global Instance Show_option (T : Type) {S : Show T} : Show (option T) :=
      fun x => option_show show x.

    Definition emit_fn_header (drop_vars:bool) (fh:fn_header) : showM :=
      show (linkage_fh fh) <<
      show (visibility_fh fh) <<
      show (cconv_fh fh) <<
      (if (unnamed_addr_fh fh) then "unnamed_addr " else empty) <<
      show (return_type_fh fh) << " " <<
      iter_show (map (fun x => show x << " ") (return_type_attrs_fh fh)) <<
      "@" << name_fh fh << "(" <<
      sepBy ", "
            (map (fun (p : type * var * list param_attr) => 
              let '(t, x, attrs) := p in
              show t <<
              (if drop_vars then empty else " %"%string << x) <<
              iter_show (map (fun x => show x << " ") attrs))
              (args_fh fh)) <<
      ") " <<
      iter_show (map (fun x => show x << " ") (attrs_fh fh)) <<
      option_show (fun s => ", section " << quoted s << " ") (section_fh fh) <<
      option_show (fun n => ", align " << show n << " ") (align_fh fh) <<
      option_show (fun s => "gc " << quoted s << " ") (gc_fh fh).

    Definition show_arith(opcode:string)(nuw nsw:bool)(ty:type)(op1 op2:value) : showM := 
      opcode << " " << flag nuw "nuw " << flag nsw "nsw " << show ty << " " <<
      show op1 << ", " << show op2.

    Definition show_binop(opcode:string)(ty:type)(op1 op2:value) : showM := 
      show_arith opcode false false ty op1 op2.

    Definition show_logical(opcode:string)(ex:bool)(ty:type)(op1 op2:value) : showM := 
      opcode << " " << flag ex "exact " << show ty << " " << show op1 << ", " << show op2.
    
    Definition show_conv(opcode:string)(ty1:type)(op:value)(ty2:type) : showM := 
      opcode << " " << show ty1 << " " << show op << " to " << show ty2.

    Global Instance Show_exp : Show exp :=
      fun e =>
        match e with 
          | Add_e nuw nsw ty op1 op2 => show_arith "add" nuw nsw ty op1 op2
          | Fadd_e ty op1 op2 => show_binop "fadd" ty op1 op2
          | Sub_e nuw nsw ty op1 op2 => show_arith "sub" nuw nsw ty op1 op2
          | Fsub_e ty op1 op2 => show_binop "fsub" ty op1 op2
          | Mul_e nuw nsw ty op1 op2 => show_arith "mul" nuw nsw ty op1 op2
          | Fmul_e ty op1 op2 => show_binop "fmul" ty op1 op2
          | Udiv_e ex ty op1 op2 => show_logical "udiv" ex ty op1 op2
          | Sdiv_e ex ty op1 op2 => show_logical "sdiv" ex ty op1 op2
          | Fdiv_e ty op1 op2 => show_binop "fdiv" ty op1 op2
          | Urem_e ty op1 op2 => show_binop "urem" ty op1 op2
          | Srem_e ty op1 op2 => show_binop "srem" ty op1 op2
          | Frem_e ty op1 op2 => show_binop "frem" ty op1 op2
          | Shl_e nuw nsw ty op1 op2 => show_arith "shl" nuw nsw ty op1 op2
          | Lshr_e ex ty op1 op2 => show_logical "lshr" ex ty op1 op2
          | Ashr_e ex ty op1 op2 => show_logical "ashr" ex ty op1 op2
          | And_e ty op1 op2 => show_binop "and" ty op1 op2
          | Or_e ty op1 op2 => show_binop "or" ty op1 op2
          | Xor_e ty op1 op2 => show_binop "xor" ty op1 op2
          | Extractvalue_e ty op n ns => 
            "extractvalue " << show ty << " " << show op << ", " <<
            sepBy ", " (List.map show (n::ns))
          | Insertvalue_e ty1 op1 ty2 op2 n ns =>
            "insertvalue " << show ty1 << " " << show op1 << ", " <<
            show ty2 << " " << show op2 << ", " <<
            sepBy ", " (List.map show (n::ns))
          | Alloca_e ty opttynum optalign => 
            "alloca " << show ty <<
            match opttynum return showM with 
              | None => "" 
              | Some (ty,n) => ", " << show ty << " " << show n
            end <<
            match optalign return showM with
              | None => "" 
              | Some n => ", align " << show n
            end
          | Load_e atomic volatile ty pointer align nontemporal invariant singlethread => 
        (* fixme: just doing the simple stuff here *)
           "load " << flag atomic "atomic " << flag volatile "volatile " <<
            show ty << " " << show pointer << " " << flag singlethread "singlethread " <<
            match align return showM with
              | None => ""
              | Some n => ", align " << show n
            end
          | Getelementptr_e inbounds ty v indexes =>
    "getelementptr " << (flag inbounds "inbounds ") << (show ty) << " " << 
            (sepBy ", " ((show v)::
              (List.map (fun p => (show (fst p)) << " " << (show (snd p))) indexes)))
          | Trunc_e ty1 v ty2 => show_conv "trunc" ty1 v ty2 
          | Zext_e ty1 v ty2 => show_conv "zext" ty1 v ty2 
          | Sext_e ty1 v ty2 => show_conv "sext" ty1 v ty2 
          | Fptrunc_e ty1 v ty2 => show_conv "fptrunc" ty1 v ty2 
          | Fpext_e ty1 v ty2 => show_conv "fpext" ty1 v ty2 
          | Fptoui_e ty1 v ty2 => show_conv "fptoui" ty1 v ty2 
          | Fptosi_e ty1 v ty2 => show_conv "fptosi" ty1 v ty2 
          | Uitofp_e ty1 v ty2 => show_conv "uitofp" ty1 v ty2 
          | Sitofp_e ty1 v ty2 => show_conv "sitofp" ty1 v ty2 
          | Ptrtoint_e ty1 v ty2 => show_conv "ptrtoint" ty1 v ty2 
          | Inttoptr_e ty1 v ty2 => show_conv "inttoptr" ty1 v ty2 
          | Bitcast_e ty1 v ty2 => show_conv "bitcast" ty1 v ty2 
          | Icmp_e cond ty v1 v2 => "icmp " << (show cond) << " " << (show ty) <<
            (show v1) << ", " << (show v2)
          | Fcmp_e cond ty v1 v2 => "fcmp " << (show cond) << " " << (show ty) <<
            (show v1) << ", " << (show v2)
          | Phi_e ty vls => 
            "phi " << show ty << " " << 
            sepBy ", " (List.map (fun p => "[ " << show (fst p) << ", " << show (snd p) << " ]") vls)
          | Select_e ty1 v1 ty2 v2 ty3 v3 => 
            "select " << (show ty1) << " " << (show v1) << ", " << 
            (show ty2) << " " << (show v2) << ", " << 
            (show ty3) << " " << (show v3)
          | Call_e tail conv ret_attrs ty fnptrty fnptr args fnattrs =>
            flag tail "tail " << "call " << option_show show conv << " " <<
            sepBy " " (List.map show ret_attrs) << " " <<
            show ty << " " << option_show show fnptrty << 
            show fnptr << "(" <<
            (sepBy ", " (List.map (fun x => match x with | (t,v,a) => 
                                            (show t) << " " << (show v) << 
                                            (sepBy " " (List.map show a))
                                          end) args)) 
            << ") " << sepBy " " (List.map show fnattrs)
        end.

    Global Instance Show_instr : Show instr :=
      fun i => 
        match i with 
          | Comment_i s => "; " << s
          | Ret_i vopt => 
            "ret " << 
            option_show (fun p => show (fst p) << " " << show (snd p)) vopt
          | Br_cond_i v l1 l2 => 
            "br i1 " << show v << ", label %" << l1 << ", label %" << l2
          | Br_uncond_i l => 
            "br label "<< l
          | Switch_i t v def arms => 
            "switch " << show t << " " << show v << ", label %" << def << " [" <<
            sepBy " " (List.map (fun p : type * Z * label => 
              let '(t,i,l) := p in
              show t << " " << show i << ", label %" << l) arms) << " ]"
          | Resume_i t v => 
            "resume " << show t << " " << show v
          | Unreachable_i => "unreachable"
          | Assign_i (Some x) e => show x << " = " << show e
          | Assign_i None e => show e
          | Store_i atomic volatile ty v ptrty pointer align nontemporal singlethread => 
            (* fix -- doesn't do nontemporal or ordering *)
            "store " << flag atomic "atomic " << flag volatile "volatile " << show ty << " " <<
            show v << ", " << show ptrty << " " << show pointer << " " <<
            flag singlethread "singlethread " << 
            option_show (fun n => ", align " << show n << " ") align
        end.

    Global Instance Show_block : Show block :=
      fun b => 
        option_show (fun l : label => "  " << l << ":" << chr_newline) (fst b) << 
        iter_show (map show (snd b)).

    Global Instance Show_topdecl : Show topdecl :=
      fun t =>
        match t return showM with 
          | Global_d x a l u c t v s al => 
            x << " = " <<
            option_show (fun n => "addrspace(" << show n << ")") a <<
            option_show show l <<
            (if u then "unnamed_addr " else empty) <<
            (if c then "constant " else empty) <<
            show t << " " << 
            show v << " " <<
            option_show (fun s => ", section " << quoted s << " ") s <<
            option_show (fun n => ", align " << show n << " ") al <<
            chr_newline 
          | Define_d fh bs => "define " <<
            emit_fn_header false fh << " {" << chr_newline << iter_show (map show bs) << "}" << chr_newline
          | Declare_d fh => "declare " << emit_fn_header true fh << chr_newline
          | Alias_d x l v t e => 
            x << " = alias " << 
            show l <<
            show v <<
            show t << " " << 
            show e << chr_newline
          | Metadata_d x cs => 
            x << " = metadata !{" << sepBy ", " (List.map show cs) << 
            "}" << chr_newline
        end.

    Global Instance Show_module : Show module :=
      fun m => iter_show (map show m).
    
    Definition string_of_module (m : module) : string := runShow (show m) "".
    Definition string_of_topdecl (t : topdecl) : string := runShow (show t) "".
    Definition string_of_fn_header (b : bool) (h : fn_header) : string := runShow (emit_fn_header b h) "".

  End Printing.
End LLVM.
