Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.

Open Scope Z_scope.
Open Scope string_scope.

Definition is_prime (a : Z) : Prop :=
  2 <= a /\ forall x : Z, 2 <= x -> x * x <= a -> Z.modulo a x <> 0.

Definition intersection_spec (interval1 interval2 : Z * Z) (result : string) : Prop :=
  let l := Z.max (fst interval1) (fst interval2) in
  let r := Z.min (snd interval1) (snd interval2) in
  (result = "YES" /\ is_prime (r - l)) \/ (result = "NO" /\ ~ is_prime (r - l)).

Example test_intersection : intersection_spec (1%Z, 2%Z) (2%Z, 3%Z) "NO".
Proof.
  unfold intersection_spec.
  simpl.
  right.
  split.
  - reflexivity.
  - unfold is_prime.
    intros [H1 H2].
    (* Z.max 1 2 = 2, Z.min 2 3 = 2, so r - l = 2 - 2 = 0 *)
    (* We need to show that 0 is not prime, i.e., ~(2 <= 0 /\ ...) *)
    (* The first condition 2 <= 0 is false *)
    lia.
Qed.