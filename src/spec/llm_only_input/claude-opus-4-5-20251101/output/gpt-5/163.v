Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import ZArith.

Definition generate_integers_spec (a b : nat) (res : list nat) : Prop :=
  let lo := Nat.min a b in
  let hi := Nat.min (Nat.max a b) 9 in
  res =
    (if Nat.leb lo hi then
       List.filter (fun i => Nat.even i) (List.seq lo (S (Nat.sub hi lo)))
     else
       nil).

(* Helper to convert Z to nat for the test *)
Definition Z_to_nat (z : Z) : nat := Z.to_nat z.

(* The test case uses Z integers, so we need to work with nat equivalents *)
(* input = [2%Z; 10%Z] means a=2, b=10 in nat *)
(* output = [2%Z; 4%Z; 6%Z; 8%Z] means [2; 4; 6; 8] in nat *)

Example test_generate_integers : generate_integers_spec 2 10 (2 :: 4 :: 6 :: 8 :: nil).
Proof.
  unfold generate_integers_spec.
  simpl.
  reflexivity.
Qed.