Require Import List.
Require Import Nat.
Import ListNotations.

Definition incr_list_spec (l : list nat) (result : list nat) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [100; 200; 300; 400; 500] [101; 201; 301; 401; 501].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.