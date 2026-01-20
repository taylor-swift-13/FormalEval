Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "Testing te stingone
twot
thrThis is a long strinThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dogg that has many characters in itee
four
five 123" 209.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.