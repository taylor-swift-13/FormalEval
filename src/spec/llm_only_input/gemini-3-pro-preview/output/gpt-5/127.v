Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.
Open Scope string_scope.

Definition is_prime (a : Z) : Prop :=
  2 <= a /\ forall x : Z, 2 <= x -> x * x <= a -> Z.modulo a x <> 0.

Definition intersection_spec (interval1 interval2 : Z * Z) (result : string) : Prop :=
  let l := Z.max (fst interval1) (fst interval2) in
  let r := Z.min (snd interval1) (snd interval2) in
  (result = "YES" /\ is_prime (r - l)) \/ (result = "NO" /\ ~ is_prime (r - l)).

Example test_case : intersection_spec (1, 2) (2, 3) "NO".
Proof.
  unfold intersection_spec.
  simpl.
  (* The intersection length is Z.min 2 3 - Z.max 1 2 = 2 - 2 = 0 *)
  (* We need to prove the right side of the disjunction: "NO" = "NO" /\ ~ is_prime 0 *)
  right.
  split.
  - reflexivity.
  - unfold is_prime.
    intro H.
    destruct H as [H1 H2].
    (* H1 : 2 <= 0, which is false *)
    lia.
Qed.