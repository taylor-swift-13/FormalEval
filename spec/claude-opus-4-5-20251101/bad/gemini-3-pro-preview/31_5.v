Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Fixpoint no_divisor_in_range (n : Z) (d : Z) (count : nat) : bool :=
  match count with
  | O => true
  | S count' => 
      (negb (Z.rem n d =? 0)) && no_divisor_in_range n (d + 1) count'
  end.

Lemma no_divisor_in_range_correct : forall n d count,
  no_divisor_in_range n d count = true ->
  forall k, d <= k < d + Z.of_nat count -> Z.rem n k <> 0.
Proof.
  induction count as [| count' IH].
  - intros. lia.
  - intros H_chk k H_range.
    simpl in H_chk.
    apply andb_true_iff in H_chk. destruct H_chk as [H_curr H_rec].
    apply negb_true_iff in H_curr. apply Z.eqb_neq in H_curr.
    assert (H_split : k = d \/ d + 1 <= k) by lia.
    destruct H_split as [H_eq | H_gt].
    + subst. assumption.
    + apply IH; try assumption.
      rewrite Nat2Z.inj_succ in H_range.
      lia.
Qed.

Example test_is_prime_61 : is_prime_spec 61 true.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: n <= 1 *)
    intros H.
    lia.
  - (* Case: n > 1 *)
    intros _.
    split.
    + (* result = true -> forall d ... *)
      intros _.
      intros d H_ge_2 H_lt_n.
      apply (no_divisor_in_range_correct 61 2 59).
      * vm_compute. reflexivity.
      * lia.
    + (* forall d ... -> result = true *)
      intros _.
      reflexivity.
Qed.