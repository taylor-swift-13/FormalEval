Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint pos_to_binary (p : positive) : string :=
  match p with
  | xH => "1"
  | xO p' => append (pos_to_binary p') "0"
  | xI p' => append (pos_to_binary p') "1"
  end.

Definition Z_to_binary (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => pos_to_binary p
  | Zneg p => pos_to_binary p
  end.

Definition decimal_to_binary_spec (decimal : Z) (result : string) : Prop :=
  decimal >= 0 /\
  result = append "db" (append (Z_to_binary decimal) "db").

Example test_case_0 : decimal_to_binary_spec 1000000000001 "db1110100011010100101001010001000000000001db".
Proof.
  unfold decimal_to_binary_spec.
  split.
  - lia.
  - unfold Z_to_binary.
    simpl.
    reflexivity.
Qed.