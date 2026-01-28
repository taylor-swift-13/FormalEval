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

Definition test_input : list Z := [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z].

Example test_case : search_spec test_input 3%Z.
Proof.
  unfold search_spec.
  intros H_exists.
  
  (* We first prove that 3 is a valid candidate to use in both parts of the proof *)
  assert (H_valid_3: valid_candidate 3 test_input).
  {
    unfold valid_candidate.
    split; [lia | ].
    split.
    - unfold test_input. simpl. tauto.
    - unfold count_occurrences, test_input. simpl. lia.
  }

  split.
  - split.
    + (* Prove result (3) is valid *)
      exact H_valid_3.
    + (* Prove result (3) is maximal among valid candidates *)
      intros m H_valid_m.
      unfold valid_candidate in H_valid_m.
      destruct H_valid_m as [H_pos [H_in H_count]].
      unfold test_input in H_in, H_count.
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
    exists 3.
    exact H_valid_3.
Qed.