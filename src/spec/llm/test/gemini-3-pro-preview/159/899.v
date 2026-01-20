Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 802 702 801 [1504; 99].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    (* 802 + 702 = 1504 and 801 - 702 = 99 *)
    reflexivity.
  - (* Case: need > remaining *)
    intros H.
    (* The hypothesis 702 > 801 is false *)
    lia.
Qed.