Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Fixpoint check_range (n : Z) (start : Z) (count : nat) : bool :=
  match count with
  | O => true
  | S count' => 
      if (n mod start =? 0) then false 
      else check_range n (start + 1) count'
  end.

Lemma check_range_correct : forall n start count,
  check_range n start count = true ->
  forall d, start <= d < start + Z.of_nat count -> n mod d <> 0.
Proof.
  intros n start count H_check d H_range.
  revert start H_check d H_range.
  induction count as [|count' IH]; intros start H_check d H_range.
  - simpl in H_range; lia.
  - simpl in H_check.
    destruct (n mod start =? 0) eqn:H_div.
    + discriminate H_check.
    + apply Z.eqb_neq in H_div.
      destruct (Z.eq_dec d start) as [H_eq|H_neq].
      * subst d; assumption.
      * apply IH with (start := start + 1).
        -- assumption.
        -- rewrite Nat2Z.inj_succ in H_range. lia.
Qed.

Example test_case : x_or_y_spec 7919 (-1) 12 (-1).
Proof.
  unfold x_or_y_spec.
  split.
  - intros H_prime. reflexivity.
  - intros H_not_prime.
    exfalso.
    apply H_not_prime.
    unfold is_prime.
    split.
    + lia.
    + intros d H_ge_2 H_sq.
      assert (d < 89).
      {
        assert (89 * 89 = 7921) by reflexivity.
        nia.
      }
      assert (H_check : check_range 7919 2 87 = true).
      { vm_compute. reflexivity. }
      apply check_range_correct with (start := 2) (count := 87) (d := d) in H_check.
      * assumption.
      * lia.
Qed.