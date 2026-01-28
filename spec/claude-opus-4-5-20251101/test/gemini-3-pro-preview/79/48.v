Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint Z_to_binary_aux (n : Z) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
    if Z.eqb n 0 then ""
    else let bit := if Z.eqb (Z.modulo n 2) 0 then "0" else "1" in
         append (Z_to_binary_aux (Z.div n 2) fuel') bit
  end.

(* Helper functions to calculate sufficient fuel efficiently *)
Fixpoint pos_depth (p : positive) : nat :=
  match p with
  | xH => 1
  | xO p' => S (pos_depth p')
  | xI p' => S (pos_depth p')
  end.

Definition Z_depth (n : Z) : nat :=
  match n with
  | Z0 => 0
  | Zpos p => pos_depth p
  | Zneg p => pos_depth p
  end.

(* Use efficient fuel calculation based on log2 of n *)
Definition Z_to_binary (n : Z) : string :=
  if Z.eqb n 0 then "0"
  else Z_to_binary_aux n (Z_depth n + 1).

Definition decimal_to_binary_spec (decimal : Z) (result : string) : Prop :=
  decimal >= 0 /\
  result = append "db" (append (Z_to_binary decimal) "db").

Example test_case_0 : decimal_to_binary_spec 1000000006 "db111011100110101100101000000110db".
Proof.
  unfold decimal_to_binary_spec.
  split.
  - (* Prove 1000000006 >= 0 *)
    lia.
  - (* Prove result string construction *)
    unfold Z_to_binary.
    (* Use vm_compute for efficient evaluation with the optimized fuel *)
    vm_compute.
    reflexivity.
Qed.