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
  problem_138_spec 20%Z true.
Proof.
  unfold problem_138_spec.
  split.
  - intros _. exists 2%Z, 4%Z, 6%Z, 8%Z.
    repeat split.
    exists 1%Z. split; [lia| lia].
    exists 2%Z. split; [lia| lia].
    exists 3%Z. split; [lia| lia].
    exists 4%Z. split; [lia| lia].
    lia.
  - intros _. reflexivity.
Qed.