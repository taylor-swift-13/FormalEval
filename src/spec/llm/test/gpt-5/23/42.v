Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition s_test : string :=
  "one" ++ nl ++ "twot This striThis is a long streing that has many characters in itng has a " ++ nl ++
  " newline character" ++ nl ++ "three" ++ nl ++ "four" ++ nl ++ "five".

Example strlen_spec_new: strlen_spec s_test 115.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length s_test) = 115%Z.
Proof.
  simpl.
  reflexivity.
Qed.