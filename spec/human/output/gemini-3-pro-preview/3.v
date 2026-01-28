Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_empty: problem_3_spec [] false.
Proof.
  unfold problem_3_spec.
  split.
  - (* Forward direction: (exists prefix suffix ...) -> false = true *)
    intros [prefix [suffix [Happ Hlt]]].
    (* If prefix ++ suffix is empty, then prefix must be empty *)
    apply app_eq_nil in Happ.
    destruct Happ as [Hprefix _].
    subst prefix.
    (* Simplify the sum of an empty prefix *)
    simpl in Hlt.
    (* 0 < 0 is a contradiction *)
    lia.
  - (* Backward direction: false = true -> (exists ...) *)
    intros H.
    (* false = true is impossible *)
    discriminate H.
Qed.