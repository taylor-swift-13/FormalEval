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

Example test_mixed_list : below_zero_spec [99; 100; -50; 20; -10] false.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intros [prefix [suffix [Heq Hsum]]].
      unfold sum_list in Hsum.
      destruct prefix as [|z1 t1].
      * simpl in Hsum. lia.
      * simpl in Heq. injection Heq as Hz1 Heq. subst z1.
        destruct t1 as [|z2 t2].
        { simpl in Hsum. lia. }
        simpl in Heq. injection Heq as Hz2 Heq. subst z2.
        destruct t2 as [|z3 t3].
        { simpl in Hsum. lia. }
        simpl in Heq. injection Heq as Hz3 Heq. subst z3.
        destruct t3 as [|z4 t4].
        { simpl in Hsum. lia. }
        simpl in Heq. injection Heq as Hz4 Heq. subst z4.
        destruct t4 as [|z5 t5].
        { simpl in Hsum. lia. }
        simpl in Heq. injection Heq as Hz5 Heq. subst z5.
        destruct t5 as [|z6 t6].
        { simpl in Hsum. lia. }
        simpl in Heq. discriminate Heq.
  - split.
    + intros _ prefix suffix Heq.
      unfold sum_list.
      destruct prefix as [|z1 t1].
      * simpl. lia.
      * simpl in Heq. injection Heq as Hz1 Heq. subst z1.
        destruct t1 as [|z2 t2].
        { simpl. lia. }
        simpl in Heq. injection Heq as Hz2 Heq. subst z2.
        destruct t2 as [|z3 t3].
        { simpl. lia. }
        simpl in Heq. injection Heq as Hz3 Heq. subst z3.
        destruct t3 as [|z4 t4].
        { simpl. lia. }
        simpl in Heq. injection Heq as Hz4 Heq. subst z4.
        destruct t4 as [|z5 t5].
        { simpl. lia. }
        simpl in Heq. injection Heq as Hz5 Heq. subst z5.
        destruct t5 as [|z6 t6].
        { simpl. lia. }
        simpl in Heq. discriminate Heq.
    + intro H. reflexivity.
Qed.