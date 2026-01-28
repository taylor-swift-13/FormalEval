Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Lra.

Import ListNotations.

Open Scope R_scope.

(* Predicates is_list_min and is_list_max *)
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

Example test_problem_21 : problem_21_spec [2.0; 49.9] [0.0; 1.0].
Proof.
  unfold problem_21_spec.
  exists 2.0, 49.9.
  split.
  - (* Prove is_list_min *)
    unfold is_list_min. split.
    + simpl. left. reflexivity.
    + intros x H. simpl in H.
      destruct H as [H | [H | H]]; try contradiction.
      * rewrite <- H. lra.
      * rewrite <- H. lra.
  - split.
    + (* Prove is_list_max *)
      unfold is_list_max. split.
      * simpl. right. left. reflexivity.
      * intros x H. simpl in H.
        destruct H as [H | [H | H]]; try contradiction.
        -- rewrite <- H. lra.
        -- rewrite <- H. lra.
    + (* Prove output calculation *)
      simpl.
      f_equal.
      * (* First element: 0.0 = (2.0 - 2.0) / (49.9 - 2.0) *)
        field.
        lra. (* Prove denominator 49.9 - 2.0 <> 0 *)
      * f_equal.
        -- (* Second element: 1.0 = (49.9 - 2.0) / (49.9 - 2.0) *)
           field.
           lra. (* Prove denominator 49.9 - 2.0 <> 0 *)
        -- (* End of list *)
           reflexivity.
Qed.