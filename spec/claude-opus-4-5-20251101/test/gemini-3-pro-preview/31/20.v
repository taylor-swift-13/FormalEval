Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Fixpoint check_range (n : Z) (d : Z) (count : nat) : bool :=
  match count with
  | O => true
  | S c => if Z.eqb (Z.rem n d) 0 
           then false 
           else check_range n (d + 1) c
  end.

Lemma check_range_correct : forall n d count,
  check_range n d count = true ->
  forall k, d <= k < d + Z.of_nat count -> Z.rem n k <> 0.
Proof.
  intros n d count H k Hk.
  revert d H k Hk.
  induction count as [| c IH]; intros d H k Hk.
  - lia.
  - simpl in H.
    destruct (Z.eqb (Z.rem n d) 0) eqn:Heq.
    + discriminate H.
    + apply Z.eqb_neq in Heq.
      assert (k = d \/ d < k) by lia.
      destruct H0 as [Hk_eq | Hk_gt].
      * subst k. assumption.
      * apply IH with (d := d + 1).
        -- assumption.
        -- rewrite Nat2Z.inj_succ in Hk. lia.
Qed.

Example test_is_prime_1009 : is_prime_spec 1009 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros H. lia.
  - intros _.
    split.
    + intros _.
      intros d H_le H_lt.
      apply (check_range_correct 1009 2 1007).
      * vm_compute. reflexivity.
      * simpl. lia.
    + intros _. reflexivity.
Qed.