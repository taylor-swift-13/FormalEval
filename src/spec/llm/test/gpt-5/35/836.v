Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [-1001%Z; 1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 999977%Z; 7%Z; 8%Z; 999992%Z; 10%Z; 21%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 999976%Z; 19%Z; 20%Z; 15%Z; 11%Z; 15%Z; 5%Z; 11%Z] 999992%Z.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. right. right. right. right. right. right. right. right. right. left. reflexivity.
  - apply (Forall_forall (fun x : Z => x <= 999992%Z)
      [-1001%Z; 1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 999977%Z; 7%Z; 8%Z; 999992%Z; 10%Z; 21%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 999976%Z; 19%Z; 20%Z; 15%Z; 11%Z; 15%Z; 5%Z; 11%Z]).
    repeat (constructor; try lia).
Qed.