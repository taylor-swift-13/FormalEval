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

Example test_case : search_spec [1; 1; 1; 1; 2; 2; 2; 3; 3; 4; 4; 4; 4; 4; 4; 4] 4.
Proof.
  unfold search_spec.
  intros H_exists.
  
  (* We first prove that 4 is a valid candidate to use in both parts of the proof *)
  assert (H_valid_4: valid_candidate 4 [1; 1; 1; 1; 2; 2; 2; 3; 3; 4; 4; 4; 4; 4; 4; 4]).
  {
    unfold valid_candidate.
    split; [lia | ].
    split.
    - simpl. tauto.
    - unfold count_occurrences. simpl. lia.
  }

  split.
  - split.
    + (* Prove result (4) is valid *)
      exact H_valid_4.
    + (* Prove result (4) is maximal among valid candidates *)
      intros m H_valid_m.
      unfold valid_candidate in H_valid_m.
      destruct H_valid_m as [H_pos [H_in H_count]].
      simpl in H_in.
      (* Check every element in the list *)
      repeat (destruct H_in as [H_eq | H_in]; 
              [ subst; unfold count_occurrences in H_count; simpl in H_count; try lia 
              | ]).
      (* The remaining case is when the list is exhausted (H_in : False) *)
      contradiction.
  - (* Prove that if no candidate exists, result is -1 (contradiction here) *)
    intros H_not_exists.
    exfalso.
    apply H_not_exists.
    exists 4.
    exact H_valid_4.
Qed.