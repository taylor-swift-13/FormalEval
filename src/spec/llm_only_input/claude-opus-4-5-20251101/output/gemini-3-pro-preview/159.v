Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example eat_test_case : eat_spec 5 6 10 [11; 4].
Proof.
  unfold eat_spec.
  split.
  - intros H.
    (* need = 6, remaining = 10, so need <= remaining is true *)
    (* result should be [5 + 6; 10 - 6] = [11; 4] *)
    reflexivity.
  - intros H.
    (* need = 6, remaining = 10, so need > remaining is false *)
    (* This case is vacuously true since 6 > 10 is false *)
    lia.
Qed.