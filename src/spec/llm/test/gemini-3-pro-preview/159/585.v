Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 601 1000 699 [1300; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    (* 1000 <= 699 is false *)
    lia.
  - (* Case: need > remaining *)
    intros H.
    (* 601 + 699 = 1300 *)
    reflexivity.
Qed.