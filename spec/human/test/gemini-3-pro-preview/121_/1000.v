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

Example test_case : problem_121_spec [31; 42; 53; 75; 86; 97; 52; 75; 53] 137.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31. Even pos (0), Odd val. Match. 137 = 31 + 106 *)
  apply soep_match with (s_tail := 106).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 42. Odd pos (1). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 53. Even pos (2), Odd val. Match. 106 = 53 + 53 *)
      apply soep_match with (s_tail := 53).
      * reflexivity.
      * reflexivity.
      * (* Index 3: 75. Odd pos (3). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 86. Even pos (4), Even val. Skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: 97. Odd pos (5). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 52. Even pos (6), Even val. Skip. *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: 75. Odd pos (7). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 53. Even pos (8), Odd val. Match. 53 = 53 + 0 *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: nil. Base case. *)
                             apply soep_nil.
Qed.