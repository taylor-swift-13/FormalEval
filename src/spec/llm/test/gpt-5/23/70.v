Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec
  (String.append "G1The quick brown f ox jumps over the lazy dog234  has a "
    (String.append (String (Ascii.ascii_of_nat 10) EmptyString)
                   " newline character5NDKQyadEb")) 86.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z:
  Z.of_nat (String.length
    (String.append "G1The quick brown f ox jumps over the lazy dog234  has a "
      (String.append (String (Ascii.ascii_of_nat 10) EmptyString)
                     " newline character5NDKQyadEb"))) = 86%Z.
Proof.
  simpl.
  reflexivity.
Qed.