Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_odd_in_even_pos_rel : list Z -> Z -> Z -> Prop :=
| soep_nil : forall i, sum_odd_in_even_pos_rel nil i 0
| soep_match : forall h t i s_tail, Z.even i = true -> Z.even h = false ->
    sum_odd_in_even_pos_rel t (i + 1) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i (h + s_tail)
| soep_skip : forall h t i s_tail, (Z.even i = false \/ Z.even h = true) ->
    sum_odd_in_even_pos_rel t (i + 1) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i s_tail.

(* 非空整数列表 *)
Definition problem_121_pre (l : list Z) : Prop := l <> [].

Definition problem_121_spec (l : list Z) (output : Z) : Prop :=
  sum_odd_in_even_pos_rel l 0 output.

Example test_case : problem_121_spec [0; 1; 2; 1; -1; 1; 1; 1; 1; 1; 1; 1] 2.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 0. Position even (0), Value even (0). Apply skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 1: Value 1. Position odd (1). Apply skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 2: Value 2. Position even (2), Value even (2). Apply skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 3: Value 1. Position odd (3). Apply skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 4: Value -1. Position even (4), Value odd (-1). Apply match. *)
  (* We need -1 + 3 = 2, so s_tail must be 3. *)
  apply soep_match with (s_tail := 3).
  - reflexivity.
  - reflexivity.
  - (* Index 5: Value 1. Position odd (5). Apply skip. *)
    apply soep_skip. { left. reflexivity. }
    (* Index 6: Value 1. Position even (6), Value odd (1). Apply match. *)
    (* We need 1 + 2 = 3, so s_tail must be 2. *)
    apply soep_match with (s_tail := 2).
    + reflexivity.
    + reflexivity.
    + (* Index 7: Value 1. Position odd (7). Apply skip. *)
      apply soep_skip. { left. reflexivity. }
      (* Index 8: Value 1. Position even (8), Value odd (1). Apply match. *)
      (* We need 1 + 1 = 2, so s_tail must be 1. *)
      apply soep_match with (s_tail := 1).
      * reflexivity.
      * reflexivity.
      * (* Index 9: Value 1. Position odd (9). Apply skip. *)
        apply soep_skip. { left. reflexivity. }
        (* Index 10: Value 1. Position even (10), Value odd (1). Apply match. *)
        (* We need 1 + 0 = 1, so s_tail must be 0. *)
        apply soep_match with (s_tail := 0).
        -- reflexivity.
        -- reflexivity.
        -- (* Index 11: Value 1. Position odd (11). Apply skip. *)
           apply soep_skip. { left. reflexivity. }
           (* Index 12: Empty list. Base case. *)
           apply soep_nil.
Qed.