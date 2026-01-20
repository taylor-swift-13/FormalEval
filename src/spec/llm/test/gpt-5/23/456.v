Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_Bro1s: strlen_spec "Bro1s" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Bro1s_Z: Z.of_nat (String.length "Bro1s") = 5%Z.
Proof.
  simpl.
  reflexivity.
Qed.