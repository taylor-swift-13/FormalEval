Require Import List.
Require Import Nat.
Import ListNotations.

Definition incr_list_spec (l : list nat) (result : list nat) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_nonzero : incr_list_spec [0; 0; 0; 6; 0; 0] [1; 1; 1; 7; 1; 1].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.