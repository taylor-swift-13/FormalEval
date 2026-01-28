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

Definition my_list : list Z := [7%Z; 9%Z; 9%Z; 5%Z; 6%Z; 8%Z; 2%Z; 10%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 8%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z].

Example test_case : search_spec my_list 4.
Proof.
  unfold search_spec.
  intros H_exists.

  assert (H_valid_res: valid_candidate 4 my_list).
  {
    unfold valid_candidate.
    split; [lia | ].
    split.
    - unfold my_list. simpl. tauto.
    - unfold count_occurrences, my_list. vm_compute. lia.
  }

  split.
  - split.
    + exact H_valid_res.
    + intros m H_valid_m.
      unfold valid_candidate in H_valid_m.
      destruct H_valid_m as [H_pos [H_in H_count]].
      unfold my_list in H_in.
      repeat (destruct H_in as [H_eq | H_in]; 
              [ subst; unfold count_occurrences, my_list in H_count; vm_compute in H_count; try lia 
              | ]).
      contradiction.
  - intros H_not_exists.
    exfalso.
    apply H_not_exists.
    exists 4.
    exact H_valid_res.
Qed.