Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.

Open Scope Z_scope.
Open Scope string_scope.

Definition fruit_distribution_spec (s : string) (n : Z) (mangoes : Z) : Prop :=
  let words := True in
  exists c1 c2 : Z,
    0 <= c1 /\ 0 <= c2 /\
    n - c1 - c2 >= 0 /\
    mangoes = n - c1 - c2.

Example test_fruit_distribution : 
  fruit_distribution_spec "15 apples and 8 oranges" 49 26.
Proof.
  unfold fruit_distribution_spec.
  exists 15, 8.
  repeat split; try lia.
Qed.