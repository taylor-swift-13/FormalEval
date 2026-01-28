Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition has_even_length (s : string) : bool :=
  Nat.even (String.length s).

Definition cmp_strings (s t : string) : comparison :=
  let len_s := String.length s in
  let len_t := String.length t in
  match Nat.compare len_s len_t with
  | Lt => Lt
  | Gt => Gt
  | Eq => String.compare s t
  end.

Fixpoint is_sorted_by (cmp : string -> string -> comparison) (l : list string) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: (y :: _) as tl => 
      (cmp x y = Lt \/ cmp x y = Eq) /\ is_sorted_by cmp tl
  end.

Definition is_permutation_of_filtered (original filtered : list string) : Prop :=
  forall s, In s filtered <-> (In s original /\ has_even_length s = true).

Definition sorted_list_sum_spec (lst : list string) (result : list string) : Prop :=
  (forall s, In s result <-> (In s lst /\ has_even_length s = true)) /\
  is_sorted_by cmp_strings result.

Example test_case : sorted_list_sum_spec ["the"; "quick"; "hello"; "fox"; "jumps"; "over"; "the"; "lazy"; "dog"; "the"] ["lazy"; "over"].
Proof.
  unfold sorted_list_sum_spec.
  split.
  - (* Verify the filtering condition *)
    intros s.
    split.
    + (* Forward direction: In result -> In input /\ even length *)
      intros H.
      simpl in H.
      destruct H as [H | [H | H]].
      * (* Case s = "lazy" *)
        subst.
        split.
        -- simpl. do 7 right. left. reflexivity.
        -- compute. reflexivity.
      * (* Case s = "over" *)
        subst.
        split.
        -- simpl. do 5 right. left. reflexivity.
        -- compute. reflexivity.
      * (* Case In s [] (contradiction) *)
        contradiction.
    + (* Backward direction: In input /\ even length -> In result *)
      intros [H_in H_even].
      simpl in H_in.
      repeat (destruct H_in as [H_eq | H_in]; [subst | ]).
      * (* "the" *) compute in H_even. discriminate H_even.
      * (* "quick" *) compute in H_even. discriminate H_even.
      * (* "hello" *) compute in H_even. discriminate H_even.
      * (* "fox" *) compute in H_even. discriminate H_even.
      * (* "jumps" *) compute in H_even. discriminate H_even.
      * (* "over" *) simpl. right. left. reflexivity.
      * (* "the" *) compute in H_even. discriminate H_even.
      * (* "lazy" *) simpl. left. reflexivity.
      * (* "dog" *) compute in H_even. discriminate H_even.
      * (* "the" *) compute in H_even. discriminate H_even.
      * (* Empty *) contradiction.
  - (* Verify the sorting condition *)
    simpl.
    split.
    + left. compute. reflexivity.
    + trivial.
Qed.