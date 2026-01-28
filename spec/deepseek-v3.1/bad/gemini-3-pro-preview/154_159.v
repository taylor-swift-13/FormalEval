Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.

Local Open Scope string_scope.
Local Open Scope nat_scope.

Definition string_append : string -> string -> string := String.append.
Definition string_length : string -> nat := String.length.
Definition string_eq : string -> string -> bool := String.eqb.

Definition string_in (s1 s2 : string) : bool :=
  match String.index 0 s1 s2 with
  | Some _ => true
  | None => false
  end.

Definition cycpattern_check_spec (a : string) (b : string) (result : bool) : Prop :=
  (string_eq a b = true -> result = true) /\
  (string_eq b "" = true -> result = true) /\
  (forall (i : nat), (i < string_length b)%nat -> 
    string_in (string_append (substring i (string_length b - i) b) 
                            (substring 0 i b)) a = true -> result = true) /\
  ((string_eq a b = false) -> 
   (string_eq b "" = false) -> 
   (forall (i : nat), (i < string_length b)%nat -> 
    string_in (string_append (substring i (string_length b - i) b) 
                            (substring 0 i b)) a = false) -> result = false).

Definition s1 := "bbbaaaaccbbaaaccccabbaaacccccbbaaabbbaaaaccbbaaaccccabbaaacccccbbaaaaccccbbaaaaccccbbaaaccccbbaaaccccbbaaaccccbbaaabcaccccbbaaaaccccbothmicgloabaaaccccbbaaaccccbbaothmicgloaaaccccbbaaabc".
Definition s2 := "bbbaaaaccbbaaaccccabbaaacccccbbaaabbbaaaaccbbaaaccccabbaaacccccbbaaaaccccbbaaaaccccbbaaaccccbbaaaccccbbaaaccccbbaaabcaccccbbaaaaccccbothmicgloabaaaccccbbaaaccccbbaothmicgloaaaccccbbaaabc".

Fixpoint check_rotations_range (n : nat) (b a : string) : bool :=
  match n with
  | 0 => true
  | S n' => 
      let i := n' in
      let rot := string_append (substring i (string_length b - i) b) (substring 0 i b) in
      match string_in rot a with
      | true => false
      | false => check_rotations_range n' b a
      end
  end.

Lemma check_rotations_range_correct : forall n b a,
  check_rotations_range n b a = true ->
  forall i, i < n ->
  string_in (string_append (substring i (string_length b - i) b) (substring 0 i b)) a = false.
Proof.
  induction n; intros b a Hcheck i Hi.
  - lia.
  - simpl in Hcheck.
    destruct (string_in (string_append (substring n (string_length b - n) b) (substring 0 n b)) a) eqn:Hrot.
    + discriminate.
    + destruct (Nat.eq_dec i n).
      * subst. assumption.
      * apply IHn; try assumption. lia.
Qed.

Example test_cycpattern_check : cycpattern_check_spec s1 s2 false.
Proof.
  unfold cycpattern_check_spec.
  split.
  {
    intro H.
    unfold s1, s2 in H.
    vm_compute in H.
    discriminate.
  }
  split.
  {
    intro H.
    unfold s2 in H.
    vm_compute in H.
    discriminate.
  }
  split.
  {
    intros i Hi HIn.
    assert (Hcheck: check_rotations_range (string_length s2) s2 s1 = true).
    { unfold s1, s2. vm_compute. reflexivity. }
    pose proof (check_rotations_range_correct _ _ _ Hcheck i Hi) as HFalse.
    rewrite HIn in HFalse.
    discriminate.
  }
  {
    intros Hneq Hnotempty Hforall.
    reflexivity.
  }
Qed.