Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition problem_53_pre (x : bool) (y : Z) : Prop := True.

Definition problem_53_spec (x : bool) (y : Z) (output : Z) : Prop :=
  output = (if x then 1 else 0) + y.

Example problem_53_test_case_1 :
  let input := [true; 6%Z] in
  let output := 7%Z in
  problem_53_pre (hd false input) (hd 0%Z (tl input)) ->
  problem_53_spec (hd false input) (hd 0%Z (tl input)) output.
Proof.
  intros.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.