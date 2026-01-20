Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 749 299 800 [1048; 501].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    reflexivity.
  - (* Case: need > remaining *)
    intros H.
    lia.
Qed.