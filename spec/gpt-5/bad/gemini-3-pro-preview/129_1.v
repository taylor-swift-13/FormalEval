Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Import ListNotations.

Definition nth_matrix (grid : list (list nat)) (i j : nat) : option nat :=
  match nth_error grid i with
  | Some row => nth_error row j
  | None => None
  end.

Definition opt_to_list_nat (o : option nat) : list nat :=
  match o with
  | Some x => x :: nil
  | None => nil
  end.

Definition minPath_spec (grid : list (list nat)) (k : nat) (ans : list nat) : Prop :=
  let N := length grid in
  2 <= N /\
  Forall (fun row => length row = N) grid /\
  NoDup (concat grid) /\
  Forall (fun v => 1 <= v /\ v <= N * N) (concat grid) /\
  exists x y mn,
    x < N /\ y < N /\
    nth_matrix grid x y = Some 1 /\
    let nx := if Nat.ltb 0 x then nth_matrix grid (x - 1) y else None in
    let px := if Nat.ltb (S x) N then nth_matrix grid (x + 1) y else None in
    let ny := if Nat.ltb 0 y then nth_matrix grid x (y - 1) else None in
    let py := if Nat.ltb (S y) N then nth_matrix grid x (y + 1) else None in
    let neighbors :=
      app (opt_to_list_nat nx)
          (app (opt_to_list_nat px)
               (app (opt_to_list_nat ny) (opt_to_list_nat py))) in
    In mn neighbors /\
    (forall u, In u neighbors -> mn <= u) /\
    ans = map (fun i => if Nat.even i then 1 else mn) (seq 0 k).

Example test_minPath : minPath_spec 
  [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] 
  3 
  [1; 2; 1].
Proof.
  unfold minPath_spec.
  simpl.
  split.
  - lia.
  - split.
    + repeat constructor.
    + split.
      * (* NoDup *)
        repeat constructor; intro H; simpl in H; intuition discriminate.
      * split.
        -- (* Forall range *)
           repeat constructor; lia.
        -- (* Exists *)
           exists 0, 0, 2.
           repeat split.
           ++ lia.
           ++ lia.
           ++ reflexivity.
           ++ (* In 2 [4; 2] *)
              simpl. right. left. reflexivity.
           ++ (* forall u, In ... *)
              intros u H. simpl in H.
              destruct H as [H | [H | H]]; try contradiction; subst; lia.
           ++ reflexivity.
Qed.