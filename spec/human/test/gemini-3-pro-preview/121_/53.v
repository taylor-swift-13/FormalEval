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

Example test_case : problem_121_spec [4; 10; 11; 18; 18] 11.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 4. Position is even (0), Value is even (4). Apply skip. *)
  apply soep_skip.
  - (* Verify condition: value is even *)
    right. reflexivity.
  - (* Recurse to tail *)
    (* Index 1: Value 10. Position is odd (1). Apply skip. *)
    apply soep_skip.
    + (* Verify condition: index is odd *)
      left. reflexivity.
    + (* Recurse to tail *)
      (* Index 2: Value 11. Position is even (2), Value is odd (11). Apply match. *)
      (* We need 11 + 0 = 11, so s_tail must be 0. *)
      apply soep_match with (s_tail := 0).
      * (* Verify index is even *)
        reflexivity.
      * (* Verify value is odd *)
        reflexivity.
      * (* Recurse to tail *)
        (* Index 3: Value 18. Position is odd (3). Apply skip. *)
        apply soep_skip.
        -- (* Verify condition: index is odd *)
           left. reflexivity.
        -- (* Recurse to tail *)
           (* Index 4: Value 18. Position is even (4), Value is even (18). Apply skip. *)
           apply soep_skip.
           ++ (* Verify condition: value is even *)
              right. reflexivity.
           ++ (* Recurse to tail *)
              (* Index 5: Empty list. Base case. *)
              apply soep_nil.
Qed.