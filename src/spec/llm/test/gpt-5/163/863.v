Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition generate_integers_spec (a b : Z) (res : list Z) : Prop :=
  let lo := Z.min a b in
  let hi := Z.min (Z.max a b) 9%Z in
  res =
    (if Z.leb lo hi then
       List.filter (fun i => Z.even i)
         (List.map Z.of_nat (List.seq (Z.to_nat lo) (S (Z.to_nat (hi - lo)))))
     else
       nil).

Example generate_integers_spec_example :
  generate_integers_spec 987654321%Z 999%Z [].
Proof.
  unfold generate_integers_spec.
  simpl.
  reflexivity.
Qed.