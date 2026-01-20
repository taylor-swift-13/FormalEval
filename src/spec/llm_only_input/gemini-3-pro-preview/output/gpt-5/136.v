Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition largest_smallest_integers_spec (lst : list Z) (a b : option Z) : Prop :=
  (
    (a = None /\ forall n, In n lst -> n < 0 -> False)
    \/
    exists m, a = Some m /\ In m lst /\ m < 0 /\ forall n, In n lst -> n < 0 -> n <= m
  )
  /\
  (
    (b = None /\ forall n, In n lst -> n > 0 -> False)
    \/
    exists p, b = Some p /\ In p lst /\ p > 0 /\ forall n, In n lst -> n > 0 -> p <= n
  ).

Example test_largest_smallest_integers: 
  largest_smallest_integers_spec [2; 4; 1; 3; 5; 7] None (Some 1).
Proof.
  unfold largest_smallest_integers_spec.
  split.
  - (* Case for 'a' (largest negative): None *)
    left. split.
    + reflexivity.
    + intros n H_in H_neg.
      simpl in H_in.
      (* Manually destruct the list membership to avoid automation issues *)
      destruct H_in as [H | H]; [subst; lia | ].
      destruct H as [H | H]; [subst; lia | ].
      destruct H as [H | H]; [subst; lia | ].
      destruct H as [H | H]; [subst; lia | ].
      destruct H as [H | H]; [subst; lia | ].
      destruct H as [H | H]; [subst; lia | ].
      destruct H. (* H is False here *)
  - (* Case for 'b' (smallest positive): Some 1 *)
    right. exists 1.
    split. { reflexivity. }
    split. { 
      simpl. 
      (* Navigate to 1 in the list: 2, 4, 1 *)
      right. right. left. reflexivity. 
    }
    split. { lia. }
    intros n H_in H_pos.
    simpl in H_in.
    (* Verify 1 <= n for all positive n in the list *)
    destruct H_in as [H | H]; [subst; lia | ].
    destruct H as [H | H]; [subst; lia | ].
    destruct H as [H | H]; [subst; lia | ].
    destruct H as [H | H]; [subst; lia | ].
    destruct H as [H | H]; [subst; lia | ].
    destruct H as [H | H]; [subst; lia | ].
    destruct H.
Qed.