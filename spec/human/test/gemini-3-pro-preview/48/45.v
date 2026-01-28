Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

(* Pre: no special constraints for `is_palindrome` *)
Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  (*
    output is true if and only if:
    for all natural numbers i, if i is less than half the string length,
    then the character at position i must equal the character at position (length - 1 - i).
  *)
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example test_problem_48 : problem_48_spec "Was it a car or a cat I saw?rr" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H 0).
    assert (Hcond : (0 < String.length "Was it a car or a cat I saw?rr" / 2)%nat).
    { vm_compute. repeat constructor. }
    apply H in Hcond.
    vm_compute in Hcond.
    inversion Hcond.
Qed.