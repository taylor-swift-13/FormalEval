Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

(* Helper function: checks if n has any divisor in the range [2, n-1] by iterating over a list *)
Definition check_prime_range (n : Z) : bool :=
  forallb (fun x => negb (Z.rem n (Z.of_nat x) =? 0)) (seq 2 (Z.to_nat n - 2)).

(* Lemma: if check_prime_range returns true, then no divisor exists in the range *)
Lemma check_prime_range_correct : forall n,
  1 < n ->
  check_prime_range n = true ->
  (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0).
Proof.
  intros n Hn Hcheck d Hge Hlt.
  unfold check_prime_range in Hcheck.
  rewrite forallb_forall in Hcheck.
  (* Instantiate the check for the specific divisor d (converted to nat) *)
  specialize (Hcheck (Z.to_nat d)).
  assert (Hin: In (Z.to_nat d) (seq 2 (Z.to_nat n - 2))).
  {
    apply in_seq.
    split.
    - (* Prove 2 <= Z.to_nat d *)
      change 2%nat with (Z.to_nat 2).
      apply Z2Nat.inj_le; lia.
    - (* Prove Z.to_nat d < 2 + len *)
      assert (Hlen: (2 + (Z.to_nat n - 2) = Z.to_nat n)%nat).
      {
        (* Since n > 1, Z.to_nat n >= 2 *)
        assert (Hn_nat: (Z.to_nat n >= 2)%nat).
        { change 2%nat with (Z.to_nat 2). apply Z2Nat.inj_le; lia. }
        lia.
      }
      rewrite Hlen.
      apply Z2Nat.inj_lt; lia.
  }
  specialize (Hcheck Hin).
  (* Simplify the boolean check back to the proposition *)
  rewrite Z2Nat.id in Hcheck; [|lia].
  apply negb_true_iff in Hcheck.
  apply Z.eqb_neq in Hcheck.
  exact Hcheck.
Qed.

Example test_is_prime_8999 : is_prime_spec 8999 true.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: n <= 1 *)
    intros H. lia.
  - (* Case: n > 1 *)
    intros _.
    split.
    + (* Direction: result = true -> forall d ... *)
      intros _.
      apply check_prime_range_correct.
      * lia.
      * (* Verify the check by computation *)
        vm_compute. reflexivity.
    + (* Direction: (forall d ...) -> result = true *)
      intros _. reflexivity.
Qed.