Require Import List.
Require Import Nat.
Import ListNotations.

Definition incr_list_spec (l : list nat) (result : list nat) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_simple : incr_list_spec [1; 1; 0; 0] [2; 2; 1; 1].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.