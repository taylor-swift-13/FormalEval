Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "Step12zZ2petssaw@@@@!3j  12zZ2@@@@!Able was I ere I saw Elba.j3jd3!@@@2Zz21" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "Step12zZ2petssaw@@@@!3j  12zZ2@@@@!Able was I ere I saw Elba.j3jd3!@@@2Zz21") / 2)%nat as Hi.
    { 
      (* The length of the string is clearly greater than 1, so 0 < length / 2 holds. *)
      simpl.
      apply Nat.lt_0_succ.
    }
    apply H in Hi.
    (* The first character does not match the last character, proving the string is not a palindrome. *)
    discriminate Hi.
Qed.