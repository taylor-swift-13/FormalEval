Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Lra.

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

Example test_case_1 :
  problem_21_spec [2.0; 49.9] [0.0; 1.0].
Proof.
  unfold problem_21_spec.
  exists 2.0, 49.9.
  split.
  - split.
    + simpl. left. reflexivity.
    + intros x Hx. simpl in Hx. destruct Hx as [H2 | [H49 | Hnil]].
      * rewrite H2. lra.
      * rewrite H49. lra.
      * contradiction.
  - split.
    + split.
      * simpl. right. left. reflexivity.
      * intros x Hx. simpl in Hx. destruct Hx as [H2 | [H49 | Hnil]].
        -- rewrite H2. lra.
        -- rewrite H49. lra.
        -- contradiction.
    + simpl. reflexivity.
Qed.