Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Lia.
Import ListNotations.

Definition longest_spec (input : list (list ascii)) (output : option (list ascii)) : Prop :=
  (input = [] /\ output = None) \/
  (exists out i,
    output = Some out /\
    length input > 0 /\
    i < length input /\
    nth_error input i = Some out /\
    (forall j, j < length input -> exists s, nth_error input j = Some s -> length s <= length out) /\
    (forall j, j < i -> exists s, nth_error input j = Some s -> length s < length out)
  ).

Example test_longest_empty :
  longest_spec [] None.
Proof.
  unfold longest_spec.
  left.
  split.
  - reflexivity.
  - reflexivity.
Qed.