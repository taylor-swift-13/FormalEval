Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition seqZ (start : Z) (len : nat) : list Z :=
  List.map (fun i => start + Z.of_nat i) (List.seq 0 len).

Definition generate_integers_spec (a b : Z) (res : list Z) : Prop :=
  let lo := Z.min a b in
  let hi := Z.min (Z.max a b) 9%Z in
  res =
    (if Z.leb lo hi then
       List.filter (fun i => Z.even i) (seqZ lo (Z.to_nat (hi - lo + 1)))
     else
       nil).

Example generate_integers_spec_example :
  generate_integers_spec 10000%Z 987654319%Z [].
Proof.
  unfold generate_integers_spec.
  simpl.
  reflexivity.
Qed.