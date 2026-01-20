
Require Import List ZArith.
Import ListNotations.

Definition make_a_pile_spec (n : Z) (result : list Z) : Prop :=
  n > 0 /\
  result = map (fun i => n + 2 * Z.of_nat i) (seq 0 (Z.to_nat n)).
