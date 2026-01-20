Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_1 : strlen_spec " cJH1th1s 4         funthec    ls !nsampleto 1t
" 48.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.