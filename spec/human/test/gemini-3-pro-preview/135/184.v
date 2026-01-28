Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition drop_at (lst : list Z) (k : nat) : Prop :=
  (1 <= k)%nat /\ (k < length lst)%nat /\
  match nth_error lst k, nth_error lst (k - 1) with
  | Some y, Some x => (y < x)%Z
  | _, _ => False
  end.

Definition problem_135_pre (lst : list Z) : Prop := NoDup lst.

Definition problem_135_spec (lst : list Z) (r : Z) : Prop :=
  (r = -1 /\ (forall k, ~ drop_at lst k))
  \/
  (exists k : nat,
      r = Z.of_nat k /\
      drop_at lst k /\
      (forall j : nat, drop_at lst j -> (j <= k)%nat)).

Example test_problem_135 : problem_135_spec [3; 6; 9; 12; 15; 21; 19; 16; 13; 10; 7; 4; 1; 2; 5; 8; 11; 14; 17; 20] 12.
Proof.
  unfold problem_135_spec.
  right.
  exists 12%nat.
  split.
  - reflexivity.
  - split.
    + unfold drop_at. simpl. split; [lia | split; [lia | lia]].
    + intros j H.
      unfold drop_at in H.
      destruct H as [Hge [Hlt Hcond]].
      simpl in Hlt.
      assert (j <= 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 19)%nat as Hcases by lia.
      destruct Hcases as [Hle | [H13 | [H14 | [H15 | [H16 | [H17 | [H18 | H19]]]]]]].
      * assumption.
      * subst j. simpl in Hcond. lia.
      * subst j. simpl in Hcond. lia.
      * subst j. simpl in Hcond. lia.
      * subst j. simpl in Hcond. lia.
      * subst j. simpl in Hcond. lia.
      * subst j. simpl in Hcond. lia.
      * subst j. simpl in Hcond. lia.
Qed.