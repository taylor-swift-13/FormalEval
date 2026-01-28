Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_long : strlen_spec "Hello, WoG1234 This sitriThis is a long string that has many characters in itng h as a 
 newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazby Thisthree
four
fiveracter dogQyadEborlod!" 236.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.