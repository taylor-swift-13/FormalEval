Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_Fow1thF1Thisxuk: strlen_spec "Fow1thF1Thisxuk"%string 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Fow1thF1Thisxuk_Z: Z.of_nat (String.length "Fow1thF1Thisxuk"%string) = 15%Z.
Proof.
  simpl.
  reflexivity.
Qed.