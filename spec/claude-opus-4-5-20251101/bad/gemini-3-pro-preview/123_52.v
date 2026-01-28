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

Example test_collatz_27348 : get_odd_collatz_spec 27348 [1; 5; 7; 11; 13; 17; 37; 43; 49; 65; 271; 361; 407; 481; 611; 641; 917; 6837].
Proof.
  unfold get_odd_collatz_spec.
  split.
  - lia.
  - exists [27348; 13674; 6837; 20512; 10256; 5128; 2564; 1282; 641; 1924; 962; 481; 1444; 722; 361; 1084; 542; 271; 814; 407; 1222; 611; 1834; 917; 2752; 1376; 688; 344; 172; 86; 43; 130; 65; 196; 98; 49; 148; 74; 37; 112; 56; 28; 14; 7; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
    split.
    + repeat (apply collatz_step; [lia | simpl]).
      apply collatz_one.
    + exists [6837; 641; 481; 361; 271; 407; 611; 917; 43; 65; 49; 37; 7; 11; 17; 13; 5; 1].
      split.
      * vm_compute. reflexivity.
      * split.
        -- unfold is_permutation. intro x.
           simpl.
           destruct (Z.eq_dec 1 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 5 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 7 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 11 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 13 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 17 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 37 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 43 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 49 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 65 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 271 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 361 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 407 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 481 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 611 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 641 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 917 x); [subst; vm_compute; reflexivity | ].
           destruct (Z.eq_dec 6837 x); [subst; vm_compute; reflexivity | ].
           vm_compute; reflexivity.
        -- repeat constructor; lia.
Qed.