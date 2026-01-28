Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint triples_sum_to_zero (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs =>
      let fix check_pairs (target : Z) (l' : list Z) : bool :=
        match l' with
        | [] => false
        | y :: ys =>
            let fix check_one (target' : Z) (l'' : list Z) : bool :=
              match l'' with
              | [] => false
              | z :: zs => if z =? target' then true else check_one target' zs
              end in
            if check_one (target - y) ys then true else check_pairs target ys
        end in
      if check_pairs (0 - x) xs then 1 else triples_sum_to_zero xs
  end.

Example test_case: triples_sum_to_zero [615; 4; 6; 5; 14; 12; 6] = 0.
Proof.
  reflexivity.
Qed.