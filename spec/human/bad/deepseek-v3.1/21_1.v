Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.Arith.Arith.

Import ListNotations.

Open Scope R_scope.

Definition is_list_min (l : list R) (m : R) : Prop :=
  In m l /\ (forall x, In x l -> m <= x).

Definition is_list_max (l : list R) (m : R) : Prop :=
  In m l /\ (forall x, In x l -> m >= x).

Definition problem_21_pre (input : list R) : Prop := (length input >= 2)%nat.

Definition problem_21_spec (input output : list R) : Prop :=
  exists min_val max_val,
    is_list_min input min_val /\
    is_list_max input max_val /\
    (output = map (fun x => (x - min_val) / (max_val - min_val)) input).

Example test_rescale_unit : 
  problem_21_spec [2.0; 49.9] [0.0; 1.0].
Proof.
  unfold problem_21_spec.
  exists 2.0, 49.9.
  split.
  - unfold is_list_min.
    split.
    + simpl. left. reflexivity.
    + intros x Hx.
      simpl in Hx.
      destruct Hx as [Hx|Hx].
      * rewrite Hx. apply Rle_refl.
      * destruct Hx as [Hx|Hx].
        rewrite Hx. 
        assert (2.0 <= 49.9) by (apply Rlt_le; lra).
        assumption.
        contradiction.
  - split.
    + unfold is_list_max.
      split.
      * simpl. right. left. reflexivity.
      * intros x Hx.
        simpl in Hx.
        destruct Hx as [Hx|Hx].
        rewrite Hx.
        assert (2.0 <= 49.9) by (apply Rlt_le; lra).
        assumption.
        destruct Hx as [Hx|Hx].
        rewrite Hx. apply Rle_refl.
        contradiction.
    + simpl.
      assert (Hdiff : 49.9 - 2.0 = 47.9) by lra.
      rewrite Hdiff.
      assert (Hcalc1 : (2.0 - 2.0) / 47.9 = 0).
      { field. lra. }
      assert (Hcalc2 : (49.9 - 2.0) / 47.9 = 1).
      { field. lra. }
      rewrite Hcalc1, Hcalc2.
      reflexivity.
Qed.