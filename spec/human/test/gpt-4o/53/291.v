Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example problem_53_test_case_1 :
  let input := [true; true] in
  let output := 2%Z in
  problem_53_pre (if hd false input then 1%Z else 0%Z) (if hd false (tl input) then 1%Z else 0%Z) ->
  problem_53_spec (if hd false input then 1%Z else 0%Z) (if hd false (tl input) then 1%Z else 0%Z) output.
Proof.
  intros.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.