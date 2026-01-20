Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_quick_brown_f_ox: strlen_spec "The quick brown f ox jumps over the lazy dog" 44.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_quick_brown_f_ox_Z: Z.of_nat (String.length "The quick brown f ox jumps over the lazy dog") = 44%Z.
Proof.
  simpl.
  reflexivity.
Qed.