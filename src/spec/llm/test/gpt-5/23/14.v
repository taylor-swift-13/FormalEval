Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition s_multiline : string :=
  String.append "one"
    (String.append nl
      (String.append "two"
        (String.append nl
          (String.append "three"
            (String.append nl
              (String.append "f"
                (String.append nl "foive"))))))).

Example strlen_spec_multiline: strlen_spec s_multiline 21.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_multiline_Z: Z.of_nat (String.length s_multiline) = 21%Z.
Proof.
  simpl.
  reflexivity.
Qed.