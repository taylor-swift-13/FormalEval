Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition triples_sum_to_zero (l : list Z) : Z :=
  let fix loop1 l1 :=
    match l1 with
    | [] => 0
    | x :: xs =>
      let fix loop2 l2 :=
        match l2 with
        | [] => 0
        | y :: ys =>
          let fix loop3 l3 :=
            match l3 with
            | [] => 0
            | z :: zs =>
              if x + y + z =? 0 then 1 else loop3 zs
            end
          in
          if loop3 ys =? 1 then 1 else loop2 ys
        end
      in
      if loop2 xs =? 1 then 1 else loop1 xs
    end
  in loop1 l.

Example test_case_0 : triples_sum_to_zero [1] = 0.
Proof.
  reflexivity.
Qed.