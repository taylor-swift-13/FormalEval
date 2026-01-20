Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_hello_W123345orld: strlen_spec "Hello, W123345orld!" 19.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_hello_W123345orld_Z: Z.of_nat (String.length "Hello, W123345orld!") = 19%Z.
Proof.
  simpl.
  reflexivity.
Qed.