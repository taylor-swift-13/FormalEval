Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Permutation.
Import ListNotations.

Fixpoint lex_le (s1 s2 : list ascii) : Prop :=
  match s1, s2 with
  | [], _ => True
  | _::_, [] => False
  | c1::s1', c2::s2' =>
    match Ascii.compare c1 c2 with
    | Lt => True
    | Gt => False
    | Eq => lex_le s1' s2'
    end
  end.

Definition string_le (s1 s2 : list ascii) : Prop :=
  match Nat.compare (length s1) (length s2) with
  | Lt => True
  | Gt => False
  | Eq => lex_le s1 s2
  end.

Inductive Sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
| sorted_nil : Sorted R []
| sorted_one : forall x, Sorted R [x]
| sorted_cons : forall x y l, R x y -> Sorted R (y :: l) -> Sorted R (x :: y :: l).

Definition has_even_length (s : list ascii) : bool :=
  Nat.even (length s).

Definition Spec (lst_in lst_out : list (list ascii)) : Prop :=
  Permutation lst_out (filter has_even_length lst_in) /\
  Sorted string_le lst_out.

Example sorted_list_sum_test :
  Spec [["a"%char; "p"%char; "p"%char; "l"%char; "e"%char];
        ["c"%char; "h"%char; "e"%char; "r"%char; "r"%char; "y"%char];
        ["g"%char; "r"%char; "a"%char; "p"%char; "e"%char];
        ["k"%char; "i"%char; "w"%char; "i"%char];
        ["l"%char; "e"%char; "m"%char; "o"%char; "n"%char]]
       [["k"%char; "i"%char; "w"%char; "i"%char];
        ["c"%char; "h"%char; "e"%char; "r"%char; "r"%char; "y"%char]].
Proof.
  unfold Spec.
  split.
  - simpl.
    apply perm_swap.
  - apply sorted_cons.
    + simpl. reflexivity.
    + apply sorted_one.
Qed.