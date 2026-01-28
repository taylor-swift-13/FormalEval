Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Definition divides (d n : nat) : Prop :=
  exists k, n = d * k.

Definition is_prime_spec (n : nat) (b : bool) : Prop :=
  b = true <-> 
    1 < n /\
    (forall d, 1 < d < n -> ~ divides d n).

Example test_is_prime_5 : is_prime_spec 5 true.
Proof.
  unfold is_prime_spec.
  split.
  - intro H.
    split.
    + lia.
    + intros d H_bounds H_div.
      destruct H_div as [k H_eq].
      assert (d = 2 \/ d = 3 \/ d = 4) as H_cases by lia.
      destruct H_cases as [H2 | [H3 | H4]]; subst d; lia.
  - intro H.
    reflexivity.
Qed.