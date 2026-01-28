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

Example test_case : search_spec [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 3] 3.
Proof.
  unfold search_spec.
  intros H_exists.
  
  assert (H_valid_3: valid_candidate 3 [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 3]).
  {
    unfold valid_candidate.
    split; [lia | ].
    split.
    - simpl. tauto.
    - unfold count_occurrences. simpl. lia.
  }

  split.
  - split.
    + exact H_valid_3.
    + intros m H_valid_m.
      unfold valid_candidate in H_valid_m.
      destruct H_valid_m as [H_pos [H_in H_count]].
      simpl in H_in.
      repeat (destruct H_in as [H_eq | H_in]; 
              [ subst; try lia 
              | ]).
      contradiction.
  - intros H_not_exists.
    exfalso.
    apply H_not_exists.
    exists 3.
    exact H_valid_3.
Qed.