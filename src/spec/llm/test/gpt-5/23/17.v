Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_three_four_five: strlen_spec "three
four
five" 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_three_four_five_Z: Z.of_nat (String.length "three
four
five") = 15%Z.
Proof.
  simpl.
  reflexivity.
Qed.