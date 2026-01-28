Require Import List.
Require Import Nat.
Import ListNotations.

Definition incr_list_spec (l : list nat) (result : list nat) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_custom : incr_list_spec [200; 1; 1; 1; 1; 1] [201; 2; 2; 2; 2; 2].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.