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
  smallest_change_spec [3; 1; 5; 7; 10; 10; 8; 6; 4; 32; 5; 5] 6.
Proof.
  (* Unfold the specification definition *)
  unfold smallest_change_spec.
  
  (* Simplify the expression. 
     This evaluates:
     1. length [3;...;5] to 12
     2. Nat.div 12 2 to 6
     3. rev [3;...;5] to [5;5;32;4;6;8;10;10;7;5;1;3]
     4. firstn 6 [3;...;5] to [3;1;5;7;10;10]
     5. firstn 6 [5;...;3] to [5;5;32;4;6;8]
     6. count_diffs [3;1;5;7;10;10] [5;5;32;4;6;8]
  *)
  simpl.
  
  (* The result of simpl is 6 = 6 *)
  reflexivity.
Qed.