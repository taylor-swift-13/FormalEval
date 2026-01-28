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

Example test_case : search_spec [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 11; 3; 3; 4; 4; 4; 4; 4; 4; 5; 5; 5; 6; 6; 6; 12; 7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 13] 4.
Proof.
  unfold search_spec.
  intros H_exists.
  
  assert (H_valid_res: valid_candidate 4 [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 11; 3; 3; 4; 4; 4; 4; 4; 4; 5; 5; 5; 6; 6; 6; 12; 7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 13]).
  {
    unfold valid_candidate.
    split; [lia | ].
    split.
    - simpl. tauto.
    - unfold count_occurrences. simpl. lia.
  }

  split.
  - split.
    + exact H_valid_res.
    + intros m H_valid_m.
      unfold valid_candidate in H_valid_m.
      destruct H_valid_m as [H_pos [H_in H_count]].
      simpl in H_in.
      repeat (destruct H_in as [H_eq | H_in]; 
              [ subst; unfold count_occurrences in H_count; simpl in H_count; try lia 
              | ]).
      contradiction.
  - intros H_not_exists.
    exfalso.
    apply H_not_exists.
    exists 4.
    exact H_valid_res.
Qed.