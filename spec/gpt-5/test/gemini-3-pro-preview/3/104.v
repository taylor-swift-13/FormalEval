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

Example test_below_zero_false : below_zero_spec [0; 6; 0] false.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intros [prefix [suffix [Heq Hsum]]].
      destruct prefix as [|z0 p0].
      * unfold sum_list in Hsum. simpl in Hsum. lia.
      * simpl in Heq. injection Heq as Hz0 Heq. subst z0.
        destruct p0 as [|z1 p1].
        ** unfold sum_list in Hsum. simpl in Hsum. lia.
        ** simpl in Heq. injection Heq as Hz1 Heq. subst z1.
           destruct p1 as [|z2 p2].
           *** unfold sum_list in Hsum. simpl in Hsum. lia.
           *** simpl in Heq. injection Heq as Hz2 Heq. subst z2.
               destruct p2 as [|z3 p3].
               **** unfold sum_list in Hsum. simpl in Hsum. lia.
               **** simpl in Heq. discriminate Heq.
  - split.
    + intros _ prefix suffix Heq.
      destruct prefix as [|z0 p0].
      * unfold sum_list. simpl. lia.
      * simpl in Heq. injection Heq as Hz0 Heq. subst z0.
        destruct p0 as [|z1 p1].
        ** unfold sum_list. simpl. lia.
        ** simpl in Heq. injection Heq as Hz1 Heq. subst z1.
           destruct p1 as [|z2 p2].
           *** unfold sum_list. simpl. lia.
           *** simpl in Heq. injection Heq as Hz2 Heq. subst z2.
               destruct p2 as [|z3 p3].
               **** unfold sum_list. simpl. lia.
               **** simpl in Heq. discriminate Heq.
    + intro H. reflexivity.
Qed.