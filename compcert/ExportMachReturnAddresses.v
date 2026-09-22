From Coq Require Import List String ZArith.
From compcert Require Import AST Integers Mach.
From CminorImport Require Import ExportCminor MachReturnAddresses.

Import ListNotations ExportCminor.
Local Open Scope string_scope.

(** Each row identifies a global, a suffix after a call, and a formal Asm offset. *)
Fixpoint function_rows (index : nat) (f : Mach.function) (body : Mach.code)
    (skip : nat) : list string :=
  match body with
  | [] => []
  | Mcall _ _ :: rest =>
      let address := match predict_return_address f rest with
        | Some value => offset value
        | None => "ERROR" end in
      node "row" [number (Z.of_nat index); number (Z.of_nat (S skip)); address] ::
        function_rows index f rest (S skip)
  | _ :: rest => function_rows index f rest (S skip)
  end.

Fixpoint program_rows (definitions : list (ident * globdef Mach.fundef unit))
    (index : nat) : list string :=
  match definitions with
  | [] => []
  | (_, Gfun (Internal f)) :: rest =>
      function_rows index f (Mach.fn_code f) O ++ program_rows rest (S index)
  | _ :: rest => program_rows rest (S index)
  end.

Definition program_addresses (p : Mach.program) : string :=
  node "list" (program_rows (prog_defs p) O).
