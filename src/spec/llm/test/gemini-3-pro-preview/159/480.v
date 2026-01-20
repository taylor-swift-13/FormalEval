Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 598 599 502 [1100; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    (* The hypothesis 599 <= 502 is false, proving the implication trivially *)
    lia.
  - (* Case: need > remaining *)
    intros H.
    (* 598 + 502 = 1100, so the lists match *)
    reflexivity.
Qed.