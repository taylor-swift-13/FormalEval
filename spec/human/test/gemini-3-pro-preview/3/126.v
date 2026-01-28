Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; -15%Z; 7%Z; 8%Z; 9%Z; -18%Z; 21%Z; -19%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [H1 H2]]].
    (* We must prove that no prefix has a sum < 0. We iterate through all possible prefixes by destructing 'prefix'. *)
    repeat (
      destruct prefix as [|p prefix];
      [ 
        (* Case: prefix is empty (or became empty after stripping elements). 
           Check if current accumulated sum < 0. *)
        simpl in H2; lia
      | 
        (* Case: prefix is non-empty (p :: prefix).
           Match the head of the list with the expected element from the input list 'l' in H1. *)
        simpl in H1;
        match goal with
        | [ H : _ :: _ = [] |- _ ] => 
            (* If the input list is exhausted but prefix is not, this is impossible. *)
            discriminate
        | [ H : _ :: _ = _ :: _ |- _ ] => 
            (* If both have heads, injectivity gives us p = head and the tail equation.
               Substitute p and simplify the sum H2 for the next iteration. *)
            injection H as ? H; subst; simpl in H2
        end
      ]
    ).
  - intros H. discriminate.
Qed.