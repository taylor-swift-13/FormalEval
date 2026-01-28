Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Lia.
Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example problem_53_test :
  let input := [1000001%Z; -97%Z] in
  let output := 999904%Z in
  problem_53_pre (nth 0 input 0%Z) (nth 1 input 0%Z)
  /\ problem_53_spec (nth 0 input 0%Z) (nth 1 input 0%Z) output.
Proof.
  simpl.
  split.
  - unfold problem_53_pre. trivial.
  - unfold problem_53_spec. lia.
Qed.