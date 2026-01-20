Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (n : Z) (lst : list Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec lst n).

Definition valid_candidate (n : Z) (lst : list Z) : Prop :=
  n > 0 /\ In n lst /\ count_occurrences n lst >= n.

Definition search_spec (lst : list Z) (result : Z) : Prop :=
  (exists n, valid_candidate n lst) ->
    (valid_candidate result lst /\
     forall m, valid_candidate m lst -> m <= result)
  /\
  ((~ exists n, valid_candidate n lst) -> result = -1).

Example test_search : search_spec [5; 5; 5; 5; 1] 1.
Proof.
  unfold search_spec.
  intros H_exists.
  split.
  - (* Part 1: result is valid and maximal *)
    split.
    + (* Prove valid_candidate 1 *)
      unfold valid_candidate.
      split.
      * lia. (* 1 > 0 *)
      * split.
        -- (* In 1 lst *)
           simpl. do 4 right. left. reflexivity.
        -- (* count >= 1 *)
           unfold count_occurrences. simpl. lia.
    + (* Prove maximality *)
      intros m H_valid.
      unfold valid_candidate in H_valid.
      destruct H_valid as (H_pos & H_in & H_count).
      simpl in H_in.
      (* Decompose In m lst *)
      repeat destruct H_in as [H_eq | H_in]; try subst m.
      * (* m = 5 *)
        unfold count_occurrences in H_count. simpl in H_count. lia.
      * (* m = 5 *)
        unfold count_occurrences in H_count. simpl in H_count. lia.
      * (* m = 5 *)
        unfold count_occurrences in H_count. simpl in H_count. lia.
      * (* m = 5 *)
        unfold count_occurrences in H_count. simpl in H_count. lia.
      * (* m = 1 *)
        lia.
      * (* False *)
        contradiction.
  - (* Part 2: If no candidate exists, result is -1 *)
    intros H_not_exists.
    exfalso. apply H_not_exists. exact H_exists.
Qed.