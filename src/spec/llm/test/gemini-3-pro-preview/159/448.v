Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 1 500 503 [501; 3].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    (* 1 + 500 = 501 and 503 - 500 = 3, so the lists match *)
    reflexivity.
  - (* Case: need > remaining *)
    intros H.
    (* The hypothesis 500 > 503 is false, proving the implication trivially *)
    lia.
Qed.