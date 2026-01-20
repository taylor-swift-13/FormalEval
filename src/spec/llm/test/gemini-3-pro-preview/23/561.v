Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec " cJH1th1s 4         funthec    lwiiw1ths !nsampleto 1t
" 55.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.