Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

Example test_strlen_cJH1t1sh : strlen_spec "cJH1t1sh" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.