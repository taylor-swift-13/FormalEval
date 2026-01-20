Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 601 601 750 [1202; 149].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    (* 601 + 601 = 1202 and 750 - 601 = 149, so the lists match *)
    reflexivity.
  - (* Case: need > remaining *)
    intros H.
    (* The hypothesis 601 > 750 is false, proving the implication trivially *)
    lia.
Qed.