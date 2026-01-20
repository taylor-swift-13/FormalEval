Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition zseq (start end_ : Z) : list Z :=
  List.map (fun n => Z.add start (Z.of_nat n))
           (List.seq 0 (S (Z.to_nat (Z.max 0 (end_ - start))))).

Definition generate_integers_spec (a b : Z) (res : list Z) : Prop :=
  let lo := Z.min a b in
  let hi := Z.min (Z.max a b) 9 in
  res =
    (if Z.leb lo hi then
       List.filter (fun i => Z.even i) (zseq lo hi)
     else
       nil).

Example generate_integers_spec_example :
  generate_integers_spec 987654324%Z 987654318%Z [].
Proof.
  unfold generate_integers_spec.
  simpl.
  reflexivity.
Qed.