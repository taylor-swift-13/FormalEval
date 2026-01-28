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

Example test_case : problem_121_spec [89; 1; 2; 3; 4; 6; 7] 96.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 89. Position is even (0), Value is odd (89). Apply match. *)
  (* We need 89 + 7 = 96, so s_tail must be 7. *)
  apply soep_match with (s_tail := 7).
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
      (* Index 2: Value 2. Position is even (2), Value is even (2). Apply skip. *)
      apply soep_skip.
      * (* Verify condition: value is even *)
        right. reflexivity.
      * (* Recurse to tail *)
        (* Index 3: Value 3. Position is odd (3). Apply skip. *)
        apply soep_skip.
        -- (* Verify condition: index is odd *)
           left. reflexivity.
        -- (* Recurse to tail *)
           (* Index 4: Value 4. Position is even (4), Value is even (4). Apply skip. *)
           apply soep_skip.
           ++ (* Verify condition: value is even *)
              right. reflexivity.
           ++ (* Recurse to tail *)
              (* Index 5: Value 6. Position is odd (5). Apply skip. *)
              apply soep_skip.
              ** (* Verify condition: index is odd *)
                 left. reflexivity.
              ** (* Recurse to tail *)
                 (* Index 6: Value 7. Position is even (6), Value is odd (7). Apply match. *)
                 (* We need 7 + 0 = 7, so s_tail must be 0. *)
                 apply soep_match with (s_tail := 0).
                 --- (* Verify index is even *)
                     reflexivity.
                 --- (* Verify value is odd *)
                     reflexivity.
                 --- (* Recurse to tail *)
                     (* Index 7: Empty list. Base case. *)
                     apply soep_nil.
Qed.