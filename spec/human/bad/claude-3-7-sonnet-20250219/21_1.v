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
    output = map (fun x => (x - min_val) / (max_val - min_val)) input.

Example test_problem_21 :
  problem_21_spec [2.0; 49.9] [0.0; 1.0].
Proof.
  (* Unfold the spec for clarity *)
  unfold problem_21_spec.
  (* Provide explicit witnesses for min_val and max_val *)
  eexists 2.0.
  eexists 49.9.
  repeat split.
  - (* min_val is in the list *)
    simpl; left; reflexivity.
  - (* min_val is less or equal to every element *)
    intros x Hinx.
    simpl in Hinx.
    destruct Hinx as [Hx_eq | Hinx'].
    + subst x; lra.
    + destruct Hinx' as [Hx_eq | Hinx''].
      * subst x; lra.
      * inversion Hinx''.
  - (* max_val is in the list *)
    simpl; right; left; reflexivity.
  - (* max_val is greater or equal to every element *)
    intros x Hinx.
    simpl in Hinx.
    destruct Hinx as [Hx_eq | Hinx'].
    + subst x; lra.
    + destruct Hinx' as [Hx_eq | Hinx''].
      * subst x; lra.
      * inversion Hinx''.
  - (* output equality *)
    simpl.
    f_equal; lra.
Qed.