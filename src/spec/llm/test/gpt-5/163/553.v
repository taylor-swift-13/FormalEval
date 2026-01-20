Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition generate_integers_spec (a b : nat) (res : list nat) : Prop :=
  let lo := Nat.min a b in
  let hi := Nat.min (Nat.max a b) 9 in
  res =
    (if Nat.leb lo hi then
       List.filter (fun i => Nat.even i) (List.seq lo (S (Nat.sub hi lo)))
     else
       nil).

Example generate_integers_spec_example :
  generate_integers_spec 10000 1001 [].
Proof.
  unfold generate_integers_spec.
  simpl.
  reflexivity.
Qed.