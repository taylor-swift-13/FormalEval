Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Lia.
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

Example test_can_arrange_2 : problem_135_spec [4%Z; 2%Z; 1%Z; 6%Z; 7%Z; 8%Z; 9%Z; 20%Z; 10%Z] 8%Z.
Proof.
  unfold problem_135_spec.
  right.
  exists 8%nat.
  split.
  - reflexivity.
  - split.
    + unfold drop_at.
      repeat split; try lia.
      simpl. lia.
    + intros j Hj.
      unfold drop_at in Hj.
      destruct Hj as [H1 [H2 H3]].
      simpl in H2.
      assert (j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8)%nat as Hcases by lia.
      destruct Hcases as [Hj1 | [Hj2 | [Hj3 | [Hj4 | [Hj5 | [Hj6 | [Hj7 | Hj8]]]]]]].
      * subst j. simpl in H3. lia.
      * subst j. simpl in H3. lia.
      * subst j. simpl in H3. lia.
      * subst j. simpl in H3. lia.
      * subst j. simpl in H3. lia.
      * subst j. simpl in H3. lia.
      * subst j. simpl in H3. lia.
      * subst j. lia.
Qed.