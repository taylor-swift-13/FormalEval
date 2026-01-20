Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 300 301 300 [600; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    (* The hypothesis 301 <= 300 is false, proving the implication trivially *)
    lia.
  - (* Case: need > remaining *)
    intros H.
    (* 300 + 300 = 600, so the lists match *)
    reflexivity.
Qed.