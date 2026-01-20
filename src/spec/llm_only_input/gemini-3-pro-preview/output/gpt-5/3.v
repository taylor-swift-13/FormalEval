Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_left Z.add l 0%Z.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  (result = true <-> exists prefix suffix, operations = prefix ++ suffix /\ sum_list prefix < 0%Z) /\
  (result = false <-> forall prefix suffix, operations = prefix ++ suffix -> 0%Z <= sum_list prefix).

Example test_below_zero_empty : below_zero_spec [] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Part 1: false = true <-> ... *)
    split; intro H.
    + (* Left to Right: false = true -> ... *)
      discriminate H.
    + (* Right to Left: (exists ...) -> false = true *)
      destruct H as [prefix [suffix [Heq Hsum]]].
      (* Fix: Symmetry required to apply app_eq_nil to [] = prefix ++ suffix *)
      symmetry in Heq.
      apply app_eq_nil in Heq.
      destruct Heq as [Hprefix _].
      subst prefix.
      (* Simplify sum_list [] *)
      unfold sum_list in Hsum.
      simpl in Hsum.
      (* 0 < 0 is a contradiction *)
      lia.
  - (* Part 2: false = false <-> ... *)
    split; intro H.
    + (* Left to Right: false = false -> forall ... *)
      intros prefix suffix Heq.
      (* Fix: Symmetry required to apply app_eq_nil to [] = prefix ++ suffix *)
      symmetry in Heq.
      apply app_eq_nil in Heq.
      destruct Heq as [Hprefix _].
      subst prefix.
      (* Simplify sum_list [] *)
      unfold sum_list.
      simpl.
      (* 0 <= 0 holds *)
      lia.
    + (* Right to Left: (forall ...) -> false = false *)
      reflexivity.
Qed.