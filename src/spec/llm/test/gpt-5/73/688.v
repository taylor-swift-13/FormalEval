Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (res : nat) : Prop :=
  let half := Nat.div (length arr) 2 in
  let first := firstn half arr in
  let rfirst := firstn half (rev arr) in
  res = length (filter (fun p => negb (Z.eqb (fst p) (snd p))) (combine first rfirst)).

Example smallest_change_spec_test :
  smallest_change_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 32%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 21%Z; 22%Z; 23%Z; 24%Z; 25%Z; 26%Z; 27%Z; 28%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 37%Z; 38%Z; 39%Z; 40%Z; 41%Z; 42%Z; 43%Z; 44%Z; 45%Z; 46%Z; 47%Z; 48%Z; 49%Z; 50%Z; 11%Z] 25%nat.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.