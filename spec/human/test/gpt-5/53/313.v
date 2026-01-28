Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Lia.
Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example problem_53_test :
  let input := [false; false] in
  let output := 0%Z in
  problem_53_pre (if nth 0 input false then 1%Z else 0%Z) (if nth 1 input false then 1%Z else 0%Z)
  /\ problem_53_spec (if nth 0 input false then 1%Z else 0%Z) (if nth 1 input false then 1%Z else 0%Z) output.
Proof.
  simpl.
  split.
  - unfold problem_53_pre. trivial.
  - unfold problem_53_spec. lia.
Qed.