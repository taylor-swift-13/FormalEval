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

Example test_case : search_spec [5; 5; 3; 9; 5; 6; 3; 2; 8; 5; 6; 10; 10; 6; 8; 4; 10; 7; 7; 10; 8] (-1).
Proof.
  unfold search_spec.
  intros H_exists.
  destruct H_exists as [n H_valid].
  unfold valid_candidate in H_valid.
  destruct H_valid as [H_pos [H_in H_count]].
  simpl in H_in.
  repeat (destruct H_in as [H_eq | H_in];
          [ subst; unfold count_occurrences in H_count; simpl in H_count; lia 
          | ]).
  contradiction.
Qed.