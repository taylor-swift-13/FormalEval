Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_diffs (l1 l2 : list Z) : Z :=
  match l1, l2 with
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => (if Z.eq_dec x y then 0 else 1) + count_diffs xs ys
  end.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let half_len := Nat.div (length arr) 2 in
  let prefix := firstn half_len arr in
  let suffix_reversed := firstn half_len (rev arr) in
  cnt = count_diffs prefix suffix_reversed.

Example test_smallest_change: 
  smallest_change_spec [1; 1; 2; 3; 4; 5] 3.
Proof.
  (* Unfold the specification definition *)
  unfold smallest_change_spec.
  
  (* Simplify the expression. 
     This evaluates:
     1. length [1;1;2;3;4;5] to 6
     2. Nat.div 6 2 to 3
     3. rev [1;1;2;3;4;5] to [5;4;3;2;1;1]
     4. firstn 3 [1;1;2;3;4;5] to [1;1;2]
     5. firstn 3 [5;4;3;2;1;1] to [5;4;3]
     6. count_diffs [1;1;2] [5;4;3]
        1!=5 -> 1
        1!=4 -> 1
        2!=3 -> 1
        sum = 3
  *)
  simpl.
  
  (* The result of simpl is 3 = 3 *)
  reflexivity.
Qed.