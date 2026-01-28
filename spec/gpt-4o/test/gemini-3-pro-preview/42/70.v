Require Import List.
Require Import Nat.
Import ListNotations.

Definition incr_list_spec (l : list nat) (result : list nat) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_1 : incr_list_spec [2; 2; 1; 2; 2; 2] [3; 3; 2; 3; 3; 3].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.