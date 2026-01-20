Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition generate_integers_spec (a b : Z) (res : list Z) : Prop :=
  let lo := Z.min a b in
  let hi := Z.min (Z.max a b) 9%Z in
  res =
    (if Z.leb lo hi then
       List.filter (fun i => Nat.even (Z.to_nat i))
         (List.filter (fun i => Z.leb lo i)
           (List.map Z.of_nat (List.seq 0 (S (Z.to_nat hi)))))
     else
       nil).

Example generate_integers_spec_example :
  generate_integers_spec 123456791%Z 14%Z [].
Proof.
  unfold generate_integers_spec.
  simpl.
  reflexivity.
Qed.