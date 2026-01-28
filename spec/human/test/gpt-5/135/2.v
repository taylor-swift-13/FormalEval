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
  problem_135_spec [1%Z; 2%Z; 4%Z; 5%Z] (-1)%Z.
Proof.
  unfold problem_135_spec.
  left.
  split; [reflexivity|].
  intros j Hj.
  unfold drop_at in Hj.
  destruct Hj as [Hj1 [Hjlen Hjmatch]].
  destruct j as [| j1]; [lia|].
  destruct j1 as [| j2].
  - simpl in Hjmatch. lia.
  - destruct j2 as [| j3].
    + simpl in Hjmatch. lia.
    + destruct j3 as [| j4].
      * simpl in Hjmatch. lia.
      * simpl in Hjlen. lia.
Qed.