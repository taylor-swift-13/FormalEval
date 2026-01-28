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

Example test_positive_list : below_zero_spec [1%Z; 2%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* false = true -> ... *)
      intro H. discriminate H.
    + (* exists ... -> false = true *)
      intros [prefix [suffix [Heq Hsum]]].
      destruct prefix as [|z1 [|z2 [|z3 p3]]].
      * (* prefix = [] *)
        unfold sum_list in Hsum.
        simpl in Hsum.
        lia.
      * (* prefix = [z1] *)
        simpl in Heq. inversion Heq; subst.
        unfold sum_list in Hsum. simpl in Hsum.
        lia.
      * (* prefix = [z1; z2] *)
        simpl in Heq. inversion Heq; subst.
        unfold sum_list in Hsum. simpl in Hsum.
        lia.
      * (* prefix has length >= 3 *)
        simpl in Heq.
        discriminate Heq.
  - (* Case: result = false <-> ... *)
    split.
    + (* false = false -> forall ... *)
      intros _ prefix suffix Heq.
      destruct prefix as [|z1 [|z2 [|z3 p3]]].
      * (* prefix = [] *)
        unfold sum_list.
        simpl.
        lia.
      * (* prefix = [z1] *)
        simpl in Heq. inversion Heq; subst.
        unfold sum_list. simpl.
        lia.
      * (* prefix = [z1; z2] *)
        simpl in Heq. inversion Heq; subst.
        unfold sum_list. simpl.
        lia.
      * (* prefix has length >= 3 *)
        simpl in Heq.
        discriminate Heq.
    + (* forall ... -> false = false *)
      intro H. reflexivity.
Qed.