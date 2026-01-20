Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (result : list Z) : Prop :=
  (need <= remaining -> result = [number + need; remaining - need]) /\
  (need > remaining -> result = [number + remaining; 0]).

Example test_eat_spec : eat_spec 299 499 800 [798; 301].
Proof.
  unfold eat_spec.
  split.
  - (* Case: need <= remaining *)
    intros H.
    (* 299 + 499 = 798 and 800 - 499 = 301 *)
    reflexivity.
  - (* Case: need > remaining *)
    intros H.
    (* The hypothesis 499 > 800 is false *)
    lia.
Qed.