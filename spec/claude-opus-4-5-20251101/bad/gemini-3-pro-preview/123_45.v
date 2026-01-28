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

(* Helper function to compute Collatz sequence for the witness *)
Fixpoint collatz_helper (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | 0 => []
  | S f =>
    if n =? 1 then [1]
    else n :: collatz_helper (collatz_next n) f
  end.

Example test_collatz_large : get_odd_collatz_spec 9857654321 [1; 5; 7; 11; 13; 17; 37; 131; 197; 1103; 1397; 1655; 2483; 3725; 6971; 7843; 10457; 11015; 11765; 16523; 18589; 24785; 117493; 371335; 495113; 557003; 626629; 835505; 1320301; 1760401; 2347201; 8345603; 12518405; 14836627; 22254941; 46891067; 52752451; 70336601; 79128677; 222298391; 263464759; 333447587; 351286345; 395197139; 500171381; 592795709; 1249018115; 1386232639; 1873527173; 2079348959; 2960635531; 3119023439; 3330714973; 3947514041; 4440953297; 4678535159; 7017802739; 7393240741; 9857654321; 10526704109].
Proof.
  unfold get_odd_collatz_spec.
  split.
  - lia.
  - exists (collatz_helper 9857654321 2000).
    split.
    + vm_compute.
      repeat (apply collatz_step; [lia | ]).
      apply collatz_one.
    + eexists.
      split.
      * reflexivity.
      * split.
        -- unfold is_permutation. intro x.
           simpl.
           repeat match goal with
           | [ |- context [Z.eq_dec ?a x] ] =>
               destruct (Z.eq_dec a x); [ subst; vm_compute; reflexivity | ]
           end.
           vm_compute; reflexivity.
        -- repeat constructor; lia.
Qed.