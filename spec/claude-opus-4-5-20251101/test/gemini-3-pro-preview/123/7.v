Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.

Import ListNotations.

Open Scope Z_scope.

Definition collatz_next (x : Z) : Z :=
  if Z.even x then x / 2 else x * 3 + 1.

Inductive collatz_sequence : Z -> list Z -> Prop :=
  | collatz_one : collatz_sequence 1 [1]
  | collatz_step : forall x seq,
      x > 1 ->
      collatz_sequence (collatz_next x) seq ->
      collatz_sequence x (x :: seq).

Definition is_odd (x : Z) : bool := Z.odd x.

Definition filter_odds (l : list Z) : list Z :=
  filter is_odd l.

Inductive sorted_ascending : list Z -> Prop :=
  | sorted_nil : sorted_ascending []
  | sorted_single : forall x, sorted_ascending [x]
  | sorted_cons : forall x y l,
      x <= y ->
      sorted_ascending (y :: l) ->
      sorted_ascending (x :: y :: l).

Definition is_permutation (l1 l2 : list Z) : Prop :=
  forall x, count_occ Z.eq_dec l1 x = count_occ Z.eq_dec l2 x.

Definition get_odd_collatz_spec (n : Z) (result : list Z) : Prop :=
  n > 0 /\
  exists collatz_seq : list Z,
    collatz_sequence n collatz_seq /\
    exists odds : list Z,
      odds = filter_odds collatz_seq /\
      is_permutation odds result /\
      sorted_ascending result.

(* Prevent Z.eq_dec from expanding during simpl, to keep the goal readable and manageable *)
Local Arguments Z.eq_dec : simpl never.

Example test_collatz_7 : get_odd_collatz_spec 7 [1; 5; 7; 11; 13; 17].
Proof.
  unfold get_odd_collatz_spec.
  split.
  - lia.
  - exists [7; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
    split.
    + apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_step; [lia | simpl].
      apply collatz_one.
    + exists [7; 11; 17; 13; 5; 1].
      split.
      * reflexivity.
      * split.
        -- unfold is_permutation. intro x.
           simpl.
           destruct (Z.eq_dec 7 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 11 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 17 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 13 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 5 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 1 x); [subst; vm_compute; reflexivity | ].
           vm_compute; reflexivity.
        -- repeat constructor; lia.
Qed.