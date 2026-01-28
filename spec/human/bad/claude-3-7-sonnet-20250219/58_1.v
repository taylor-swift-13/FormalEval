Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Open Scope Z_scope.

Definition problem_58_pre (l1 l2 : list Z) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list Z) : Prop :=
  (forall x: Z, In x l_out <-> (In x l1 /\ In x l2)) /\
  Sorted Z.le l_out /\
  NoDup l_out.

Definition l1 := [1;4;3;34;653;2;5].
Definition l2 := [5;7;1;5;9;653;121].
Definition l_out := [1;5;653].

(* 
   Approach:
   - Define s1 := sorted nodup of l1
   - Define s2 := sorted nodup of l2
   - intersection := set_inter s1 s2 using ListSet library
   - Show that intersection = l_out
   - Use set_inter_spec to get the properties
*)

Definition s1 : list Z := sort Z.le (nodup Z.eq_dec l1).
Definition s2 : list Z := sort Z.le (nodup Z.eq_dec l2).
Definition intersection := set_inter Z.eq_dec Z.le s1 s2.

(* Facts about s1 and s2 *)

Lemma s1_sorted : Sorted Z.le s1.
Proof. apply sort_sorted. Qed.

Lemma s1_nodup : NoDup s1.
Proof. apply sort_nodup. Qed.

Lemma s2_sorted : Sorted Z.le s2.
Proof. apply sort_sorted. Qed.

Lemma s2_nodup : NoDup s2.
Proof. apply sort_nodup. Qed.

(* Specification of intersection *)

Lemma intersection_spec :
  (forall x, In x intersection <-> In x s1 /\ In x s2) /\
  Sorted Z.le intersection /\
  NoDup intersection.
Proof.
  apply set_inter_spec; auto.
Qed.

(* Lemmas relating s1/s2 membership back to l1, l2 *)

Lemma nodup_incl (l: list Z) (x: Z) :
  In x (nodup Z.eq_dec l) <-> In x l.
Proof.
  split; intro H.
  - apply nodup_In. assumption.
  - apply nodup_In. assumption.
Qed.

Lemma s1_in_l1 x : In x s1 <-> In x l1.
Proof.
  unfold s1.
  rewrite in_sort_iff.
  split; intro H.
  - apply nodup_incl. assumption.
  - apply nodup_incl. assumption.
Qed.

Lemma s2_in_l2 x : In x s2 <-> In x l2.
Proof.
  unfold s2.
  rewrite in_sort_iff.
  split; intro H.
  - apply nodup_incl. assumption.
  - apply nodup_incl. assumption.
Qed.

(* Compute intersection to confirm it equals l_out *)
Eval compute in intersection.
(* = [1; 5; 653] *)

Example common_spec_example : problem_58_spec l1 l2 l_out.
Proof.
  unfold problem_58_spec.
  split.
  - intro x; split; intro H.
    + (* x in l_out -> x in l1 /\ x in l2 *)
      subst l_out.
      simpl in H.
      repeat
        match goal with
        | H: In _ (_ :: _) |- _ => destruct H as [H | H]
        | |- _ => idtac
        end; try (split; (repeat (apply in_cons || apply in_eq)); auto).
    + (* x in l1 /\ x in l2 -> x in l_out *)
      subst l_out.
      destruct H as [H1 H2].
      (* Use intersection_spec *)
      destruct intersection_spec as [Hinter [Hsorted Hnodup]].
      specialize (Hinter x).
      apply Hinter.
      split.
      - apply s1_in_l1. assumption.
      - apply s2_in_l2. assumption.
  - split.
    + (* sortedness *)
      subst l_out.
      repeat constructor; lia.
    + (* NoDup *)
      subst l_out.
      repeat constructor; intro Contra; inversion Contra.
Qed.