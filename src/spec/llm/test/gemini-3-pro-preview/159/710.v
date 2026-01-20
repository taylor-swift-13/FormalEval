Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 1000 199 251 [1199; 52].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    (* 1000 + 199 = 1199 and 251 - 199 = 52, so the lists match *)
    reflexivity.
  - (* Case: need > remaining *)
    intros H.
    (* The hypothesis 199 > 251 is false, proving the implication trivially *)
    lia.
Qed.