Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Lia.
Open Scope Z_scope.

Definition problem_53_pre (b : bool) (z : Z) : Prop := True.

Definition Z_of_bool (b : bool) : Z := if b then 1 else 0.

Definition problem_53_spec (b : bool) (z : Z) (output : Z) : Prop :=
  output = Z_of_bool b + z.

Example problem_53_test :
  let input_b := [true] in
  let input_z := [7%Z] in
  let output := 8%Z in
  problem_53_pre (nth 0 input_b false) (nth 0 input_z 0%Z)
  /\ problem_53_spec (nth 0 input_b false) (nth 0 input_z 0%Z) output.
Proof.
  simpl.
  split.
  - unfold problem_53_pre. trivial.
  - unfold problem_53_spec. simpl. lia.
Qed.