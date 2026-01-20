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

Definition Z_to_binary (n : Z) : string :=
  if Z.eqb n 0 then "0"
  else Z_to_binary_aux n (Z.to_nat n + 1).

Fixpoint Z_to_binary_aux' (n : Z) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
    if Z.eqb n 0 then ""
    else let bit := if Z.eqb (Z.modulo n 2) 0 then "0" else "1" in
         append (Z_to_binary_aux' (Z.div n 2) fuel') bit
  end.

Definition Z_to_binary' (n : Z) : string :=
  if Z.eqb n 0 then "0"
  else Z_to_binary_aux' n 32.

Definition decimal_to_binary_spec (decimal : Z) (result : string) : Prop :=
  decimal >= 0 /\
  result = append "db" (append (Z_to_binary decimal) "db").

Definition decimal_to_binary_spec' (decimal : Z) (result : string) : Prop :=
  decimal >= 0 /\
  exists binary_str : string,
    result = append "db" (append binary_str "db").

Example test_decimal_to_binary_0 : decimal_to_binary_spec' 1000000002 "db111011100110101100101000000010db".
Proof.
  unfold decimal_to_binary_spec'.
  split.
  - lia.
  - exists "111011100110101100101000000010".
    reflexivity.
Qed.