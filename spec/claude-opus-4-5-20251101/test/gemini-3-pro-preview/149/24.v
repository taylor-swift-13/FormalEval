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

Example test_case : sorted_list_sum_spec ["programming"; "python"; ""; "java"; "ruby"] [""; "java"; "ruby"; "python"].
Proof.
  unfold sorted_list_sum_spec.
  split.
  - (* Verify the filtering condition *)
    intros s.
    split.
    + (* Forward direction: In result -> In input /\ even length *)
      intros H.
      simpl in H.
      destruct H as [H_empty | [H_java | [H_ruby | [H_python | H_absurd]]]].
      * (* Case s = "" *)
        subst.
        split.
        -- simpl. right. right. left. reflexivity.
        -- compute. reflexivity.
      * (* Case s = "java" *)
        subst.
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- compute. reflexivity.
      * (* Case s = "ruby" *)
        subst.
        split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- compute. reflexivity.
      * (* Case s = "python" *)
        subst.
        split.
        -- simpl. right. left. reflexivity.
        -- compute. reflexivity.
      * (* Case Empty *)
        contradiction.
    + (* Backward direction: In input /\ even length -> In result *)
      intros [H_in H_even].
      simpl in H_in.
      destruct H_in as [H_prog | [H_python | [H_empty | [H_java | [H_ruby | H_absurd]]]]].
      * (* Case s = "programming" *)
        subst.
        compute in H_even.
        discriminate H_even.
      * (* Case s = "python" *)
        subst. simpl. right. right. right. left. reflexivity.
      * (* Case s = "" *)
        subst. simpl. left. reflexivity.
      * (* Case s = "java" *)
        subst. simpl. right. left. reflexivity.
      * (* Case s = "ruby" *)
        subst. simpl. right. right. left. reflexivity.
      * (* Case Empty *)
        contradiction.
  - (* Verify the sorting condition *)
    simpl.
    repeat split.
    + (* "" vs "java" *)
      left. compute. reflexivity.
    + (* "java" vs "ruby" *)
      left. compute. reflexivity.
    + (* "ruby" vs "python" *)
      left. compute. reflexivity.
Qed.