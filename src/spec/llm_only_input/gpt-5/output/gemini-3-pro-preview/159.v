Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example eat_spec_test :
  eat_spec 5%Z 6%Z 10%Z [11%Z; 4%Z].
Proof.
  unfold eat_spec.
  split.
  - intros _. compute. reflexivity.
  - intros Hgt.
    assert (6%Z <= 10%Z) by lia.
    exfalso. lia.
Qed.