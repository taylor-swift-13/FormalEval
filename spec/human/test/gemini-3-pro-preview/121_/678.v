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

Example test_case : problem_121_spec [0; 1; 2; 3; 4; 5; 6; 7; 8; 1; 2; 2] 0.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 0. Even index (0), Even value (0). Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 1: Value 1. Odd index (1). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 2: Value 2. Even index (2), Even value (2). Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 3: Value 3. Odd index (3). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 4: Value 4. Even index (4), Even value (4). Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 5: Value 5. Odd index (5). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 6: Value 6. Even index (6), Even value (6). Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 7: Value 7. Odd index (7). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 8: Value 8. Even index (8), Even value (8). Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 9: Value 1. Odd index (9). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 10: Value 2. Even index (10), Even value (2). Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 11: Value 2. Odd index (11). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 12: Empty list. Base case. *)
  apply soep_nil.
Qed.