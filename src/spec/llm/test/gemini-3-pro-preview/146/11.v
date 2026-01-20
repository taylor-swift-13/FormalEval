Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition pairs_sum_to_zero (l : list Z) : Z :=
  let fix aux l :=
    match l with
    | [] => false
    | x :: xs => if existsb (fun y => Z.eqb (x + y) 0) xs then true else aux xs
    end
  in if aux l then 0 else 1.

Example test_case_new: pairs_sum_to_zero [101; -35; 16; 44; -67] = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.