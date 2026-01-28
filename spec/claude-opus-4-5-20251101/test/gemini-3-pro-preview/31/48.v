Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Fixpoint check_no_divisors (n : Z) (current : Z) (count : nat) : bool :=
  match count with
  | O => true
  | S count' => 
      if (Z.rem n current =? 0) then false
      else check_no_divisors n (current + 1) count'
  end.

Lemma check_no_divisors_correct : forall n current count,
  check_no_divisors n current count = true ->
  forall d, current <= d < current + Z.of_nat count -> Z.rem n d <> 0.
Proof.
  intros n current count Hcheck d Hrange.
  revert current Hcheck d Hrange.
  induction count as [| count' IH]; intros current Hcheck d Hrange.
  - simpl in Hcheck. lia.
  - simpl in Hcheck.
    destruct (Z.rem n current =? 0) eqn:Hrem.
    + discriminate Hcheck.
    + apply Z.eqb_neq in Hrem.
      destruct (Z.eq_dec d current) as [Heq | Hneq].
      * rewrite Heq. assumption.
      * apply IH with (current := current + 1).
        -- assumption.
        -- lia.
Qed.

Example test_is_prime_197 : is_prime_spec 197 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros H. lia.
  - intros _. split.
    + intros _.
      intros d Hle Hlt.
      apply check_no_divisors_correct with (count := 195%nat) (current := 2).
      * vm_compute. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.