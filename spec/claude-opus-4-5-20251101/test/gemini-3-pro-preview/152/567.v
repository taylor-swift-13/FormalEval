Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition abs_diff (a b : Z) : Z :=
  Z.abs (a - b).

Fixpoint compare_spec (game : list Z) (guess : list Z) (result : list Z) : Prop :=
  match game, guess, result with
  | [], [], [] => True
  | g :: gs, gu :: gus, r :: rs => r = abs_diff g gu /\ compare_spec gs gus rs
  | _, _, _ => False
  end.

Example test_compare_spec :
  compare_spec [47; 2; 20; 501; 10; 15; 14; 10] [47; 2; 20; 501; 10; 15; 14; 10] [0; 0; 0; 0; 0; 0; 0; 0].
Proof.
  simpl.
  repeat split.
  all: unfold abs_diff; vm_compute; reflexivity.
Qed.