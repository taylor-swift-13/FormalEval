Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 501 996 502 [1003; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    (* 996 <= 502 is false, so implication holds trivially *)
    lia.
  - (* Case: need > remaining *)
    intros H.
    (* 501 + 502 = 1003, so result matches [number + remaining; 0] *)
    reflexivity.
Qed.