Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_non_palindrome :
  Spec "Evil isor a name of a fIoeman, as I live." false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "Evil isor a name of a fIoeman, as I live.") / 2)%nat.
    {
      (* Since the string is non-empty, the length is greater than 0, and half of the length is positive. *)
      unfold String.length.
      compute.
      apply Nat.lt_0_succ.
    }
    apply H in H0.
    discriminate H0.
Qed.