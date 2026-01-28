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

Example can_arrange_example_1 :
  problem_135_spec [1%Z; 2%Z; 10%Z; 9%Z; 8%Z; 6%Z; 5%Z; 3%Z] 7%Z.
Proof.
  unfold problem_135_spec.
  right.
  exists 7%nat.
  split; [reflexivity |].
  split.
  {
    unfold drop_at.
    split; [lia|].
    split; [simpl; lia|].
    simpl; lia.
  }
  {
    intros j Hj.
    destruct Hj as [Hj1 [Hjlen Hjmatch]].
    simpl in Hjlen.
    lia.
  }
Qed.