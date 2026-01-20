Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_str : string :=
  String (Ascii.ascii_of_nat 32)
    (String (Ascii.ascii_of_nat 32)
      (String (Ascii.ascii_of_nat 32)
        (String (Ascii.ascii_of_nat 10)
          (String (Ascii.ascii_of_nat 10) ("RL 1s  "))))).

Example strlen_spec_new: strlen_spec test_str 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length test_str) = 12%Z.
Proof.
  simpl.
  reflexivity.
Qed.