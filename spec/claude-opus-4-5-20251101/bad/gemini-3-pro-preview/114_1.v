Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

(* Specification Definitions *)
Definition is_subarray {A : Type} (sub arr : list A) : Prop :=
  exists prefix suffix, arr = prefix ++ sub ++ suffix.

Definition non_empty {A : Type} (l : list A) : Prop :=
  l <> [].

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition minSubArraySum_spec (nums : list Z) (result : Z) : Prop :=
  nums <> [] /\
  (exists sub : list Z, 
    non_empty sub /\ 
    is_subarray sub nums /\ 
    sum_list sub = result) /\
  (forall sub : list Z, 
    non_empty sub -> 
    is_subarray sub nums -> 
    result <= sum_list sub).

(* Helper Lemmas *)

(* Lemma: If a property holds for all elements of a list, it holds for any subarray *)
Lemma is_subarray_forall {A : Type} (P : A -> Prop) (sub arr : list A) :
  is_subarray sub arr -> Forall P arr -> Forall P sub.
Proof.
  intros [pre [suf Heq]] Hall.
  subst arr.
  apply Forall_app in Hall. destruct Hall as [_ Hrest].
  apply Forall_app in Hrest. destruct Hrest as [Hsub _].
  exact Hsub.
Qed.

(* Lemma: Sum of a list of non-negative integers is non-negative *)
Lemma sum_list_nonneg (l : list Z) :
  Forall (fun x => x >= 0) l -> sum_list l >= 0.
Proof.
  intros H. induction l.
  - simpl. lia.
  - simpl. inversion H; subst. apply IHl in H3. lia.
Qed.

(* Lemma: Sum of a non-empty list of integers >= 1 is >= 1 *)
Lemma sum_list_ge_1 (l : list Z) :
  non_empty l -> Forall (fun x => x >= 1) l -> sum_list l >= 1.
Proof.
  intros Hne Hall.
  destruct l.
  - unfold non_empty in Hne. contradiction.
  - simpl. inversion Hall; subst.
    assert (Hpos: Forall (fun x => x >= 0) l).
    { eapply Forall_impl; [| eassumption]. intros a Ha. lia. }
    apply sum_list_nonneg in Hpos.
    lia.
Qed.

(* Test Case Proof *)
Example test_min_sub_array : minSubArraySum_spec [2; 3; 4; 1; 2; 4] 1.
Proof.
  unfold minSubArraySum_spec.
  split.
  - (* Part 1: nums is not empty *)
    unfold non_empty. discriminate.
  - split.
    + (* Part 2: Existence of subarray with sum 1 *)
      exists [1].
      split.
      * unfold non_empty. discriminate.
      * split.
        -- unfold is_subarray.
           exists [2; 3; 4]. exists [2; 4].
           simpl. reflexivity.
        -- simpl. reflexivity.
    + (* Part 3: Minimality *)
      intros sub Hne Hsub.
      (* Prove all elements in the input list are >= 1 *)
      assert (Hall : Forall (fun x => x >= 1) [2; 3; 4; 1; 2; 4]).
      { repeat constructor; lia. }
      (* Deduce that all elements in the subarray are >= 1 *)
      apply (is_subarray_forall _ _ _ Hsub) in Hall.
      (* Conclude that the sum of the subarray is >= 1 *)
      apply sum_list_ge_1; assumption.
Qed.