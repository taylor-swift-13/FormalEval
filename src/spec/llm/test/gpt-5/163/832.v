Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition generate_integers_spec (a b : Z) (res : list Z) : Prop :=
  let loZ := Z.min a b in
  let hiZ := Z.min (Z.max a b) 9%Z in
  let lo := Z.to_nat (Z.max 0%Z loZ) in
  let hi := Z.to_nat (Z.max 0%Z hiZ) in
  res =
    (if Nat.leb lo hi then
       List.map Z.of_nat (List.filter (fun i => Nat.even i) (List.seq lo (S (Nat.sub hi lo))))
     else
       nil).

Example generate_integers_spec_example :
  generate_integers_spec 987654322%Z 2%Z [2%Z; 4%Z; 6%Z; 8%Z].
Proof.
  unfold generate_integers_spec.
  vm_compute.
  reflexivity.
Qed.