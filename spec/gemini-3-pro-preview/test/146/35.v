Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition triples_sum_to_zero (l : list Z) : Z :=
  let fix aux1 (l : list Z) : bool :=
    match l with
    | [] => false
    | x :: xs =>
      let fix aux2 (target : Z) (l2 : list Z) : bool :=
        match l2 with
        | [] => false
        | y :: ys =>
          let fix aux3 (target2 : Z) (l3 : list Z) : bool :=
            match l3 with
            | [] => false
            | z :: zs =>
              if Z.eqb z target2 then true else aux3 target2 zs
            end in
          if aux3 (target - y) ys then true else aux2 target ys
        end in
      if aux2 (0 - x) xs then true else aux1 xs
    end in
  if aux1 l then 1 else 0.

Example test_case_1 : triples_sum_to_zero [6%Z; 12%Z; 324%Z; 12%Z] = 0%Z.
Proof. reflexivity. Qed.