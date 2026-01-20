Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_string : string :=
  String.String (Ascii.ascii_of_nat 224)
    (String.String (Ascii.ascii_of_nat 232)
      (String.String (Ascii.ascii_of_nat 236)
        (String.String (Ascii.ascii_of_nat 242)
          (String.String (Ascii.ascii_of_nat 245)
            (String.String (Ascii.ascii_of_nat 10)
              (String.String (Ascii.ascii_of_nat 231) String.EmptyString)))))).

Example strlen_spec_new: strlen_spec test_string 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length test_string) = 7%Z.
Proof.
  simpl.
  reflexivity.
Qed.