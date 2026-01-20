Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_spaces_functoion: strlen_spec "        functoion   " 20.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_spaces_functoion_Z: Z.of_nat (String.length "        functoion   ") = 20%Z.
Proof.
  simpl.
  reflexivity.
Qed.