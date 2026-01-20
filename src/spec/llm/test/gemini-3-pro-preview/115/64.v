Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition max_fill_spec (grid : list (list Z)) (capacity : Z) (ans : Z) : Prop :=
  ans = fold_right Z.add 0 (map (fun row => (sum_list row + capacity - 1) / capacity) grid).

Example max_fill_test : max_fill_spec [[1; 1; 1]; [1; 1; 1]; [1; 1; 1]] 2 6.
Proof.
  unfold max_fill_spec.
  unfold sum_list.
  simpl.
  reflexivity.
Qed.