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

Example test_can_arrange_2 : problem_135_spec [4%Z; 6%Z; 17%Z] (-1)%Z.
Proof.
  unfold problem_135_spec.
  left.
  split.
  - reflexivity.
  - intros k Hk.
    unfold drop_at in Hk.
    destruct Hk as [H1 [H2 H3]].
    simpl in H2.
    assert (k = 1 \/ k = 2)%nat as Hcases by lia.
    destruct Hcases as [Hk1 | Hk2].
    + subst k. simpl in H3. lia.
    + subst k. simpl in H3. lia.
Qed.