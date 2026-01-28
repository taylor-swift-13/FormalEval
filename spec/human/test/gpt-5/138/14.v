Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_positive_even (e : Z) : Prop :=
  exists k : Z, e = 2 * k /\ (k > 0)%Z.

Definition problem_138_pre (n : Z) : Prop := True.

Definition problem_138_spec (n : Z) (b : bool) : Prop :=
  b = true <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\
    is_positive_even e2 /\
    is_positive_even e3 /\
    is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.

Example problem_138_test_case_0 :
  problem_138_spec 40%Z true.
Proof.
  unfold problem_138_spec.
  split.
  - intros _.
    exists 10%Z. exists 10%Z. exists 10%Z. exists 10%Z.
    repeat split; try (unfold is_positive_even; exists 5%Z; split; lia); lia.
  - intros _. reflexivity.
Qed.