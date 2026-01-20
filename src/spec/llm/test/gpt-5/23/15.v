Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_the_quick_brown_fox_jumps_overq_the_lazy_dog: strlen_spec "The quick brown fox jumps overq the lazy dog" 44.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_the_quick_brown_fox_jumps_overq_the_lazy_dog_Z: Z.of_nat (String.length "The quick brown fox jumps overq the lazy dog") = 44%Z.
Proof.
  simpl.
  reflexivity.
Qed.