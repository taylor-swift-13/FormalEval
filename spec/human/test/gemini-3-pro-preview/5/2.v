Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Open Scope Z_scope.
Import ListNotations.

Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> (1 <= n)%nat ->
      length output = (2 * n - 1)%nat /\
      forall i : nat, (i < 2 * n - 1)%nat ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

Example test_case : problem_5_spec [5; 6; 3; 2] [5; 8; 6; 8; 3; 8; 2] 8.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate.
  - intros n Hlen Hn.
    simpl in Hlen. symmetry in Hlen. subst n.
    split.
    + reflexivity.
    + intros i Hi.
      destruct i as [|i].
      { (* i = 0 *)
        split.
        - intro; reflexivity.
        - intro H; destruct H; lia.
      }
      destruct i as [|i].
      { (* i = 1 *)
        split.
        - intro H; destruct H; lia.
        - intro; reflexivity.
      }
      destruct i as [|i].
      { (* i = 2 *)
        split.
        - intro; reflexivity.
        - intro H; destruct H; lia.
      }
      destruct i as [|i].
      { (* i = 3 *)
        split.
        - intro H; destruct H; lia.
        - intro; reflexivity.
      }
      destruct i as [|i].
      { (* i = 4 *)
        split.
        - intro; reflexivity.
        - intro H; destruct H; lia.
      }
      destruct i as [|i].
      { (* i = 5 *)
        split.
        - intro H; destruct H; lia.
        - intro; reflexivity.
      }
      destruct i as [|i].
      { (* i = 6 *)
        split.
        - intro; reflexivity.
        - intro H; destruct H; lia.
      }
      (* i >= 7 *)
      lia.
Qed.