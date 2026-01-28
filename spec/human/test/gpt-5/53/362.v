Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Lia.
Open Scope Z_scope.

Definition problem_53_pre (x y : bool) : Prop := True.

Definition problem_53_spec (x : bool) (y : bool) (output : Z) : Prop :=
  output = (if x then 1 else 0) + (if y then 1 else 0).

Example problem_53_test :
  let input := [true; false] in
  let output := 1%Z in
  problem_53_pre (nth 0 input false) (nth 1 input false)
  /\ problem_53_spec (nth 0 input false) (nth 1 input false) output.
Proof.
  simpl.
  split.
  - unfold problem_53_pre. trivial.
  - unfold problem_53_spec. lia.
Qed.