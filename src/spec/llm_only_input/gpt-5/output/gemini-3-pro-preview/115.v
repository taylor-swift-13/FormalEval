Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition max_fill_spec (grid : list (list Z)) (capacity : Z) (ans : Z) : Prop :=
  ans = fold_right Z.add 0 (map (fun row => (sum_list row + capacity - 1) / capacity) grid).

Example max_fill_spec_example :
  max_fill_spec
    [[0%Z; 0%Z; 1%Z; 0%Z];
     [0%Z; 1%Z; 0%Z; 0%Z];
     [1%Z; 1%Z; 1%Z; 1%Z]]
    1%Z
    6%Z.
Proof.
  unfold max_fill_spec.
  simpl.
  repeat rewrite Z.sub_diag.
  repeat rewrite Z.add_0_r.
  repeat rewrite Z.div_1_r.
  unfold sum_list.
  simpl.
  reflexivity.
Qed.