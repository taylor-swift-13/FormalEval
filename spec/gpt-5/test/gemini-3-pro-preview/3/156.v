Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_left Z.add l 0%Z.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  (result = true <-> exists prefix suffix, operations = prefix ++ suffix /\ sum_list prefix < 0%Z) /\
  (result = false <-> forall prefix suffix, operations = prefix ++ suffix -> 0%Z <= sum_list prefix).

Example test_below_zero_true : below_zero_spec [2%Z; 3%Z; 4%Z; 5%Z; -15%Z; 7%Z; 8%Z; 9%Z; -11%Z; 21%Z; 2%Z] true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intros _.
      exists [2; 3; 4; 5; -15]%Z.
      exists [7; 8; 9; -11; 21; 2]%Z.
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + intros _. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro H.
      assert (Heq : [2; 3; 4; 5; -15; 7; 8; 9; -11; 21; 2]%Z = ([2; 3; 4; 5; -15] ++ [7; 8; 9; -11; 21; 2])%Z) by reflexivity.
      specialize (H [2; 3; 4; 5; -15]%Z [7; 8; 9; -11; 21; 2]%Z Heq).
      unfold sum_list in H. simpl in H. lia.
Qed.