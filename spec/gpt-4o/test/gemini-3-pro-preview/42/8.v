Require Import List.
Require Import Nat.
Import ListNotations.

Definition incr_list_spec (l : list nat) (result : list nat) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_basic : incr_list_spec [1; 2; 3; 4; 5; 6] [2; 3; 4; 5; 6; 7].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.