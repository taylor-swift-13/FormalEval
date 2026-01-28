Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_empty_list :
  problem_3_spec [] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Hconcat Hsum]]].
    apply app_eq_nil in Hconcat.
    destruct Hconcat as [Hpre_nil Hsuffix_nil].
    subst.
    simpl in Hsum.
    (* 0 < 0 is False *)
    elimtype False.
    omega.
  - intros H.
    inversion H.
Qed.