Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import Nat.
Require Import Lia.

Definition match_at (i : nat) (input substr : list ascii) : Prop :=
  length substr > 0 /\
  i + length substr <= length input /\
  (forall j, j < length substr -> nth_error input (i + j) = nth_error substr j).

Definition Spec (input substring : list ascii) (output : nat) : Prop :=
  exists indices : list nat,
    NoDup indices /\
    (forall i, In i indices -> match_at i input substring) /\
    (forall i, i + length substring <= length input ->
               match_at i input substring -> In i indices) /\
    output = length indices.

Example test_how_many_times_empty_string :
  Spec [] ["x"%char] 0.
Proof.
  unfold Spec.
  exists [].
  split.
  - constructor.
  - split.
    + intros i H.
      contradiction.
    + split.
      * intros i H_len H_match.
        unfold match_at in H_match.
        destruct H_match as [H_pos [H_bound H_eq]].
        simpl in H_bound.
        lia.
      * simpl.
        reflexivity.
Qed.