Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition Spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example incr_list_test_non_empty :
  Spec [2%Z; 1%Z; 1%Z; 2%Z] [3%Z; 2%Z; 2%Z; 3%Z].
Proof.