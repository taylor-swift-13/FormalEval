Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Lia.
Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Definition bool_to_Z (b : bool) : Z := if b then 1%Z else 0%Z.

Example problem_53_test :
  let input := [false; true] in
  let output := 1%Z in
  problem_53_pre (bool_to_Z (nth 0 input false)) (bool_to_Z (nth 1 input false))
  /\ problem_53_spec (bool_to_Z (nth 0 input false)) (bool_to_Z (nth 1 input false)) output.
Proof.
  simpl.
  split.
  - unfold problem_53_pre. trivial.
  - unfold problem_53_spec. simpl. lia.
Qed.