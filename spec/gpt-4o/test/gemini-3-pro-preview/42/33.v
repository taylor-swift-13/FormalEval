Require Import List.
Require Import Nat.
Import ListNotations.

Definition incr_list_spec (l : list nat) (result : list nat) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [1; 1; 1; 1; 10; 1; 1] [2; 2; 2; 2; 11; 2; 2].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.