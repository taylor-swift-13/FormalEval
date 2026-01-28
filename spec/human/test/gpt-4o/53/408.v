Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `add` *)
Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example problem_53_test_case_1 :
  let input := [10000%Z; 98765432101234567890123456788%Z] in
  let output := 98765432101234567890123466788%Z in
  problem_53_pre (hd 0%Z input) (hd 0%Z (tl input)) ->
  problem_53_spec (hd 0%Z input) (hd 0%Z (tl input)) output.
Proof.
  intros.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.