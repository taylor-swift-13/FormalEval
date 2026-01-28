Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Inductive sum_odd_in_even_pos_rel : list nat -> nat -> nat -> Prop :=
| soep_nil : forall i, sum_odd_in_even_pos_rel nil i 0%nat
| soep_match : forall h t i s_tail, Nat.even i = true -> Nat.even h = false ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i (h + s_tail)
| soep_skip : forall h t i s_tail, (Nat.even i = false \/ Nat.even h = true) ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i s_tail.

(* 非空整数列表 *)
Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  sum_odd_in_even_pos_rel l 0%nat output.

Example test_case : problem_121_spec [1; 1; 119; 88; 1; 1] 121.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 1. Position is even (0), Value is odd (1). Apply match. *)
  (* We need 1 + 120 = 121, so s_tail must be 120. *)
  apply soep_match with (s_tail := 120).
  - (* Verify index is even *)
    reflexivity.
  - (* Verify value is odd *)
    reflexivity.
  - (* Recurse to tail *)
    (* Index 1: Value 1. Position is odd (1). Apply skip. *)
    apply soep_skip.
    + (* Verify condition: index is odd *)
      left. reflexivity.
    + (* Recurse to tail *)
      (* Index 2: Value 119. Position is even (2), Value is odd (119). Apply match. *)
      (* We need 119 + 1 = 120, so s_tail must be 1. *)
      apply soep_match with (s_tail := 1).
      * (* Verify index is even *)
        reflexivity.
      * (* Verify value is odd *)
        reflexivity.
      * (* Recurse to tail *)
        (* Index 3: Value 88. Position is odd (3). Apply skip. *)
        apply soep_skip.
        -- (* Verify condition: index is odd *)
           left. reflexivity.
        -- (* Recurse to tail *)
           (* Index 4: Value 1. Position is even (4), Value is odd (1). Apply match. *)
           (* We need 1 + 0 = 1, so s_tail must be 0. *)
           apply soep_match with (s_tail := 0).
           ++ (* Verify index is even *)
              reflexivity.
           ++ (* Verify value is odd *)
              reflexivity.
           ++ (* Recurse to tail *)
              (* Index 5: Value 1. Position is odd (5). Apply skip. *)
              apply soep_skip.
              ** (* Verify condition: index is odd *)
                 left. reflexivity.
              ** (* Recurse to tail *)
                 (* Index 6: Empty list. Base case. *)
                 apply soep_nil.
Qed.