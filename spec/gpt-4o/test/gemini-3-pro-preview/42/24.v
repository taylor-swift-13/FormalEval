Require Import List.
Require Import Nat.
Import ListNotations.

Definition incr_list_spec (l : list nat) (result : list nat) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_1 : incr_list_spec [10; 100; 1000; 10] [11; 101; 1001; 11].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.