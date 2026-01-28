Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Lra.

Import ListNotations.

Open Scope R_scope.

(* 谓词 is_list_min 和 is_list_max  *)
Definition is_list_min (l : list R) (m : R) : Prop :=
  In m l /\ (forall x, In x l -> m <= x).

Definition is_list_max (l : list R) (m : R) : Prop :=
  In m l /\ (forall x, In x l -> m >= x).


(* Pre: no additional constraints for `rescale_to_unit` by default *)
Definition problem_21_pre (input : list R) : Prop := (length input >= 2)%nat.

Definition problem_21_spec (input output : list R) : Prop :=
  exists min_val max_val,
    is_list_min input min_val /\
    is_list_max input max_val /\
    (output = map (fun x => (x - min_val) / (max_val - min_val)) input).

Example test_problem_21 :
  problem_21_spec [2; (499/10)] [0; 1].
Proof.
  unfold problem_21_spec.
  exists 2, (499/10).
  split.
  - (* is_list_min [2; 499/10] 2 *)
    unfold is_list_min.
    split.
    + simpl. left. reflexivity.
    + intros x Hx.
      simpl in Hx.
      destruct Hx as [H1 | [H2 | H3]].
      * subst x. lra.
      * subst x. lra.
      * contradiction.
  - split.
    + (* is_list_max [2; 499/10] (499/10) *)
      unfold is_list_max.
      split.
      * simpl. right. left. reflexivity.
      * intros x Hx.
        simpl in Hx.
        destruct Hx as [H1 | [H2 | H3]].
        -- subst x. lra.
        -- subst x. lra.
        -- contradiction.
    + (* output = map ... input *)
      simpl.
      f_equal.
      * field. lra.
      * f_equal.
        field. lra.
Qed.