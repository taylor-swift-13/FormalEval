Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 999 999 11 [1010; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    (* 999 <= 11 is false, so the implication holds trivially *)
    lia.
  - (* Case: need > remaining *)
    intros H.
    (* 999 + 11 = 1010, so result = [1010; 0] matches *)
    reflexivity.
Qed.