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

Example test_positive_list : below_zero_spec [1; 1; 1; 1; 4; 1] false.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intros [prefix [suffix [Heq Hsum]]].
      destruct prefix as [|z0 p0].
      * unfold sum_list in Hsum. simpl in Hsum. lia.
      * simpl in Heq. injection Heq as Hz0 Heq0. subst z0.
        destruct p0 as [|z1 p1].
        { unfold sum_list in Hsum. simpl in Hsum. lia. }
        simpl in Heq0. injection Heq0 as Hz1 Heq1. subst z1.
        destruct p1 as [|z2 p2].
        { unfold sum_list in Hsum. simpl in Hsum. lia. }
        simpl in Heq1. injection Heq1 as Hz2 Heq2. subst z2.
        destruct p2 as [|z3 p3].
        { unfold sum_list in Hsum. simpl in Hsum. lia. }
        simpl in Heq2. injection Heq2 as Hz3 Heq3. subst z3.
        destruct p3 as [|z4 p4].
        { unfold sum_list in Hsum. simpl in Hsum. lia. }
        simpl in Heq3. injection Heq3 as Hz4 Heq4. subst z4.
        destruct p4 as [|z5 p5].
        { unfold sum_list in Hsum. simpl in Hsum. lia. }
        simpl in Heq4. injection Heq4 as Hz5 Heq5. subst z5.
        destruct p5 as [|z6 p6].
        { unfold sum_list in Hsum. simpl in Hsum. lia. }
        simpl in Heq5. discriminate Heq5.
  - split.
    + intros _ prefix suffix Heq.
      destruct prefix as [|z0 p0].
      * unfold sum_list. simpl. lia.
      * simpl in Heq. injection Heq as Hz0 Heq0. subst z0.
        destruct p0 as [|z1 p1].
        { unfold sum_list. simpl. lia. }
        simpl in Heq0. injection Heq0 as Hz1 Heq1. subst z1.
        destruct p1 as [|z2 p2].
        { unfold sum_list. simpl. lia. }
        simpl in Heq1. injection Heq1 as Hz2 Heq2. subst z2.
        destruct p2 as [|z3 p3].
        { unfold sum_list. simpl. lia. }
        simpl in Heq2. injection Heq2 as Hz3 Heq3. subst z3.
        destruct p3 as [|z4 p4].
        { unfold sum_list. simpl. lia. }
        simpl in Heq3. injection Heq3 as Hz4 Heq4. subst z4.
        destruct p4 as [|z5 p5].
        { unfold sum_list. simpl. lia. }
        simpl in Heq4. injection Heq4 as Hz5 Heq5. subst z5.
        destruct p5 as [|z6 p6].
        { unfold sum_list. simpl. lia. }
        simpl in Heq5. discriminate Heq5.
    + intro. reflexivity.
Qed.