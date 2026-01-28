Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition even (n : nat) : Prop :=
  Nat.even n = true.

Definition generate_integers_spec (a b : nat) (res : list nat) : Prop :=
  a > 0 /\ b > 0 /\
  res = 
    filter (fun i => Nat.even i)
           (List.filter (fun i => (a <=? i) && (i <=? (Nat.min b 9))) (seq a (S (Nat.min b 9 - a)) )) /\
  NoDup res /\
  (forall x, In x res -> a <= x <= b \/ b <= x <= a) /\
  (forall x, In x res -> even x) /\
  (forall x, even x ->
             (a <= x <= b \/ b <= x <= a) ->
             x <= 9 ->
             In x res).

Example test_case : generate_integers_spec 2 10 [2; 4; 6; 8].
Proof.
  unfold generate_integers_spec.
  repeat split.
  - (* a > 0 *)
    lia.
  - (* b > 0 *)
    lia.
  - (* res construction check *)
    simpl. reflexivity.
  - (* NoDup check *)
    repeat constructor; simpl; try tauto.
  - (* Forward range check: In x res -> range *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | H]]]]; subst; lia.
  - (* Forward even check: In x res -> even *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | H]]]]; subst; unfold even; simpl; reflexivity.
  - (* Completeness: even -> range -> <= 9 -> In x res *)
    intros x Heven Hrange Hbound.
    (* Simplify range hypothesis *)
    destruct Hrange as [H | H]; [| lia].
    
    (* Exhaustively check x for values 0 through 9 *)
    do 10 (destruct x as [|x]; [
      (* For the current natural number: *)
      (* 1. If x < 2, it violates the range (2 <= x), solved by lia *)
      try (exfalso; lia);
      (* 2. If x is odd, Heven is false = true, solved by discriminate *)
      try (simpl in Heven; discriminate);
      (* 3. If x is even and in range, it must be in the list *)
      simpl; tauto
    | ]).
    
    (* Case for x >= 10, which contradicts x <= 9 *)
    exfalso; lia.
Qed.