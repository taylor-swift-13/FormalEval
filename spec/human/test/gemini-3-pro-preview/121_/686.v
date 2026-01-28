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

Example test_case : problem_121_spec [31; 42; 3; 64; 75; 86; 97; 108; 119; 97] 325.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31. Even pos, Odd val -> Match. Tail sum = 325 - 31 = 294 *)
  apply soep_match with (s_tail := 294); [reflexivity | reflexivity | ].
  (* Index 1: 42. Odd pos -> Skip *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 2: 3. Even pos, Odd val -> Match. Tail sum = 294 - 3 = 291 *)
  apply soep_match with (s_tail := 291); [reflexivity | reflexivity | ].
  (* Index 3: 64. Odd pos -> Skip *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 4: 75. Even pos, Odd val -> Match. Tail sum = 291 - 75 = 216 *)
  apply soep_match with (s_tail := 216); [reflexivity | reflexivity | ].
  (* Index 5: 86. Odd pos -> Skip *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 6: 97. Even pos, Odd val -> Match. Tail sum = 216 - 97 = 119 *)
  apply soep_match with (s_tail := 119); [reflexivity | reflexivity | ].
  (* Index 7: 108. Odd pos -> Skip *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 8: 119. Even pos, Odd val -> Match. Tail sum = 119 - 119 = 0 *)
  apply soep_match with (s_tail := 0); [reflexivity | reflexivity | ].
  (* Index 9: 97. Odd pos -> Skip *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 10: Empty list. Base case. *)
  apply soep_nil.
Qed.