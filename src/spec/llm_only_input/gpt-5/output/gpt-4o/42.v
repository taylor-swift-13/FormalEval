Require Import List.
Require Import Nat.
Import ListNotations.

Definition incr_list_spec (l : list nat) (result : list nat) : Prop :=
  result = map (fun x => x + 1) l.

Example incr_list_spec_empty: incr_list_spec [] [].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.