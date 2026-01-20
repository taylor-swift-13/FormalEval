Require Import List.
Require Import Arith.
Require Import ZArith.

Import ListNotations.

Definition generate_integers_spec (a b : nat) (evens : list nat) : Prop :=
  let (a, b) := if a <=? b then (a, b) else (b, a) in
  evens = filter (fun i => i mod 2 =? 0) (seq a (min (b + 1) 10 - a)).

(* The test case uses Z integers, but the spec uses nat.
   We need to convert: input = [2%Z; 10%Z] means a=2, b=10
   output = [2%Z; 4%Z; 6%Z; 8%Z] means [2; 4; 6; 8] in nat *)

Example test_generate_integers : generate_integers_spec 2 10 [2; 4; 6; 8].
Proof.
  unfold generate_integers_spec.
  simpl.
  reflexivity.
Qed.