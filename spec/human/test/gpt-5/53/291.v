Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Lia.
Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example problem_53_test :
  let input := [true; true] in
  let output := 2%Z in
  problem_53_pre (Z.b2z (nth 0 input false)) (Z.b2z (nth 1 input false))
  /\ problem_53_spec (Z.b2z (nth 0 input false)) (Z.b2z (nth 1 input false)) output.
Proof.
  simpl.
  split.
  - unfold problem_53_pre. trivial.
  - unfold problem_53_spec. lia.
Qed.