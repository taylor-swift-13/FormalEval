Require Import List.
Require Import Nat.
Import ListNotations.

Definition incr_list_spec (l : list nat) (result : list nat) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [0; 400; 0; 0; 0; 0] [1; 401; 1; 1; 1; 1].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.