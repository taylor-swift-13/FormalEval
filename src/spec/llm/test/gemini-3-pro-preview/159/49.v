Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 10 5 5 [15; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    (* 10 + 5 = 15 and 5 - 5 = 0, so the lists match *)
    reflexivity.
  - (* Case: need > remaining *)
    intros H.
    (* The hypothesis 5 > 5 is false, proving the implication trivially *)
    lia.
Qed.