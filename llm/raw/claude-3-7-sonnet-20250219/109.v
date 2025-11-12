
Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.Program.Basics.

Definition sorted (l : list nat) : Prop :=
  forall i j, i < j < length l -> nth i l 0 <= nth j l 0.

Fixpoint rotate_right (l : list nat) (k : nat) : list nat :=
  let n := length l in
  if n =? 0 then l else
  let k' := k mod n in
  let split_pos := n - k' in
  (skipn split_pos l) ++ (firstn split_pos l).

Definition move_one_ball_spec (arr : list nat) (res : bool) : Prop :=
  let sorted_arr := sort Nat.leb arr in
  (res = true <->
    (arr = [] 
     \/ arr = sorted_arr
     \/ exists k, 1 <= k < length arr /\ rotate_right arr k = sorted_arr)).
