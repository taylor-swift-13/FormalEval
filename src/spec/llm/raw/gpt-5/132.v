Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.

Import ListNotations.
Local Open Scope Z_scope.

Inductive bracket := Open | Close.

Definition bracket_val (b : bracket) : Z :=
  match b with
  | Open => 1%Z
  | Close => (-1)%Z
  end.

Fixpoint prefix_sum (l : list bracket) (k : nat) : Z :=
  match l, k with
  | _, 0%nat => 0%Z
  | [], _ => 0%Z
  | b :: tl, S k' => bracket_val b + prefix_sum tl k'
  end.

Definition balanced_primitive (t : list bracket) : Prop :=
  prefix_sum t (length t) = 0%Z /\
  forall k, 1%nat <= k < length t -> 0%Z < prefix_sum t k.

Definition depth_at_least_two (t : list bracket) : Prop :=
  exists k, 1%nat <= k <= length t /\ 2%Z <= prefix_sum t k.

Definition exists_nested_block (s : list bracket) : Prop :=
  exists p t q, s = p ++ t ++ q /\ balanced_primitive t /\ depth_at_least_two t.

Definition is_nested_spec (s : list bracket) (r : bool) : Prop :=
  (r = true <-> exists_nested_block s) /\ (r = false <-> ~ exists_nested_block s).