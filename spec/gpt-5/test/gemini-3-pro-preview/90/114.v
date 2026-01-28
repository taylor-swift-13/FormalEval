Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_min_of_list (m : Z) (l : list Z) : Prop :=
  In m l /\ forall x, In x l -> m <= x.

Definition next_smallest_spec (lst : list Z) (r : option Z) : Prop :=
  match r with
  | None =>
      lst = [] \/
      (exists m, is_min_of_list m lst /\ forall x, In x lst -> x = m)
  | Some s =>
      exists m, is_min_of_list m lst /\ In s lst /\ m < s /\
                forall y, In y lst -> m < y -> s <= y
  end.

Example test_next_smallest_example:
  next_smallest_spec [5; 3; 7; 8; -80; 1; 9; -1; -10; 0] (Some (-10)).
Proof.
  unfold next_smallest_spec.
  exists (-80).
  split.
  - unfold is_min_of_list.
    split.
    + simpl. tauto.
    + intros x H.
      simpl in H.
      repeat destruct H as [H | H]; subst; lia.
  - split.
    + simpl. tauto.
    + split.
      * lia.
      * intros y HIn HGt.
        simpl in HIn.
        repeat destruct HIn as [HIn | HIn]; subst; try lia.
Qed.